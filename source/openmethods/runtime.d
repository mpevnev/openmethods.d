module openmethods.runtime;

import std.algorithm;
import std.format;
import std.range;
import std.bitmanip;

debug(explain) {
  import std.stdio;
}

debug(traceCalls) {
  import std.stdio;
}

class MethodError : Error
{
  this(int reason, const(MethodInfo)* meth) {
    super(reason.stringof);
    this.reason = reason;
    this.meth = meth;
  }

  @property string functionName() { return meth.name; }

  enum NotImplemented = 1, AmbiguousCall = 2, DeallocatorInUse = 3;
  const MethodInfo* meth;
  int reason;
  TypeInfo[] args;
}

union Word
{
  void* p;
  Word* pw;
  int i;
}

struct MethodInfo
{
  string name;
  ClassInfo[] vp;
  SpecInfo*[] specInfos;
  Word* slots;
  Word* strides;
  Word* dispatchTable;
  void* ambiguousCallError;
  void* notImplementedError;
}

struct SpecInfo
{
  void* pf;
  ClassInfo[] vp;
  void** nextPtr;
}

alias GroupMap = Class*[][BitArray];

struct Method
{
  MethodInfo* info;
  Class*[] vp;
  Spec*[] specs;

  int[] slots;
  int[] strides;
  void*[] dispatchTable;
  GroupMap firstDim;

  auto toString() const
  {
    return format("%s(%s)", info.name, vp.map!(c => c.name).join(", "));
  }
}

struct Spec
{
  SpecInfo* info;
  Class*[] params;

  auto toString() const
  {
    return format("(%s)", params.map!(c => c.name).join(", "));
  }
}

struct Param
{
  Method* method;
  int param;

  auto toString() const
  {
    return format("%s#%d", *method, param);
  }
}

struct Class
{
  ClassInfo info;
  Class*[] directBases;
  Class*[] directDerived;
  Class*[Class*] conforming;
  Param[] methodParams;
  int nextSlot = 0;
  int firstUsedSlot = -1;

  @property auto name() const
  {
    return info.name.split(".")[$ - 1];
  }

  @property auto isClass()
  {
    return info is Object.classinfo
      || info.base is Object.classinfo
      || info.base !is null;
  }
}

alias Registry = MethodInfo*[MethodInfo*];

struct HashInfo
{
  ulong hashMult;
  uint hashShift, hashSize;
  Word* hashTable;
}

struct Runtime
{
  static __gshared Registry methodInfos;
  static __gshared Word[] gmtbl; // Global Method Table
  static __gshared Word[] gdtbl; // Global Dispatch Table
  static __gshared needUpdate = true;
  static __gshared ulong hashMult;
  static __gshared uint hashShift, hashSize;
  static __gshared Word* hashTable;
  static __gshared uint methodsUsingDeallocator;
  static __gshared uint methodsUsingHash;
  Method*[] methods;
  Class*[ClassInfo] classMap;
  Class*[] classes;
  Word*[Class*] mtbls;

  void seed()
  {
    debug(explain) {
      write("Seeding...\n ");
    }

    Class* upgrade(ClassInfo ci)
    {
      Class* c;
      if (ci in classMap) {
        c = classMap[ci];
      } else {
        c = classMap[ci] = new Class(ci);
        debug(explain) {
          writef(" %s", c.name);
        }
      }
      return c;
    }

    foreach (mi; methodInfos.values) {
      auto m = new Method(mi);
      methods ~= m;

      foreach (int i, ci; mi.vp) {
        auto c = upgrade(ci);
        m.vp ~= c;
        c.methodParams ~= Param(m, i);
      }

      m.specs = mi.specInfos.map!
        (si => new Spec(si,
                        si.vp.map!
                        (ci => upgrade(ci)).array)).array;

    }

    debug(explain) {
      writeln();
    }
  }

  bool scoop(ClassInfo ci)
  {
    bool hasMethods;

    foreach (i; ci.interfaces) {
      if (scoop(i.classinfo)) {
        hasMethods = true;
      }
    }

    if (ci.base) {
      if (scoop(ci.base)) {
        hasMethods = true;
      }
    }

    if (ci in classMap) {
      hasMethods = true;
    } else if (hasMethods) {
      if (ci !in classMap) {
        auto c = classMap[ci] = new Class(ci);
        debug(explain) {
          writefln("  %s", c.name);
        }
      }
    }

    return hasMethods;
  }

  void initClasses()
  {
    foreach (ci, c; classMap) {
      foreach (i; ci.interfaces) {
        if (i.classinfo in classMap) {
          auto b = classMap[i.classinfo];
          c.directBases ~= b;
          b.directDerived ~= c;
        }
      }

      if (ci.base in classMap) {
        auto b = classMap[ci.base];
        c.directBases ~= b;
        b.directDerived ~= c;
      }
    }
  }

  void layer()
  {
    debug(explain) {
      writefln("Layering...");
    }

    auto v = classMap.values.filter!(c => c.directBases.empty).array;
    auto m = assocArray(zip(v, v));

    while (!v.empty) {
      debug(explain) {
        writefln("  %s", v.map!(c => c.name).join(" "));
      }

      v.sort!((a, b) => cmp(a.name, b.name) < 0);
      classes ~= v;

      foreach (c; v) {
        classMap.remove(c.info);
      }

      v = classMap.values.filter!(c => c.directBases.all!(b => b in m)).array;

      foreach (c; v) {
        m[c] = c;
      }
    }
  }

  void calculateInheritanceRelationships()
  {
    auto rclasses = classes.dup;
    reverse(rclasses);

    foreach (c; rclasses) {
      c.conforming[c] = c;
      foreach (d; c.directDerived) {
        c.conforming[d] = d;
        foreach (dc; d.conforming) {
          c.conforming[dc] = dc;
        }
      }
    }
  }

  void checkDeallocatorConflicts()
  {
    foreach (m; methods) {
      foreach (vp; m.vp) {
        foreach (c; vp.conforming) {
          if (c.info.deallocator
              && !(c.info.deallocator >= gmtbl.ptr
                  && c.info.deallocator <  gmtbl.ptr + gmtbl.length)) {
            throw new MethodError(MethodError.DeallocatorInUse, m.info);
          }
        }
      }
    }
  }

  void allocateSlots()
  {
    debug(explain) {
      writeln("Allocating slots...");
    }

    foreach (c; classes) {
      if (!c.methodParams.empty) {
        debug(explain) {
          writefln("  %s...", c.name);
        }

        foreach (mp; c.methodParams) {
          int slot = c.nextSlot++;

          debug(explain) {
            writef("    for %s: allocate slot %d\n    also in", mp, slot);
          }

          if (mp.method.slots.length <= mp.param) {
            mp.method.slots.length = mp.param + 1;
          }

          mp.method.slots[mp.param] = slot;

          if (c.firstUsedSlot == -1) {
            c.firstUsedSlot = slot;
          }

          bool [Class*] visited;
          visited[c] = true;

          foreach (d; c.directDerived) {
            allocateSlotDown(d, slot, visited);
          }

          debug(explain) {
            writeln();
          }
        }
      }
    }

    debug(explain) {
      writeln("Initializing the global mtbl vector...");
    }

    auto gmtblLength =
      classes.filter!(c => c.isClass).map!(c => c.nextSlot - c.firstUsedSlot).sum
      + methods.map!(m => m.vp.length).sum;

    if (methodsUsingHash) {
      findHash();
      gmtblLength += hashSize;
    }

    gmtbl.length = gmtblLength;

    Word* sp = gmtbl.ptr;

    debug(explain) {
      writefln("  gmtbl size: %d", gmtbl.length);
    }

    if (methodsUsingHash) {
      hashTable = sp;
      sp += hashSize;
      debug(explain) {
        writefln("  reserved %d entries for hash table", hashSize);
      }
    }

    debug(explain) {
      writeln("  slots:");
    }

    foreach (m; methods) {
      debug(explain) {
        writefln("    %s %02d-%02d %s",
                 sp, sp - gmtbl.ptr, sp - gmtbl.ptr + m.vp.length, *m);
      }

      m.info.slots = sp;

      foreach (slot; m.slots) {
        sp++.i = slot;
      }
    }

    debug(explain) {
      writeln("  mtbl:");
    }

    foreach (c; classes) {
      if (c.isClass) {
        debug(explain) {
          writefln("    %s %02d-%02d %s",
                   sp, c.firstUsedSlot, c.nextSlot, c.name);
        }
        auto mptr = sp - c.firstUsedSlot;
        mtbls[c] = mptr;

        if (methodsUsingDeallocator) {
          c.info.deallocator = mptr;
        }

        if (methodsUsingHash) {
          auto h = hash(c.info.vtbl.ptr);
          debug(explain) {
            writefln("    -> hashTable[%d]", h);
          }
          hashTable[h].p = mptr;
        }
        sp += c.nextSlot - c.firstUsedSlot;
      }
    }
  }

  void allocateSlotDown(Class* c, int slot, bool[Class*] visited)
  {
    if (c in visited)
      return;

    debug(explain) {
      writef(" %s", c.name);
    }

    visited[c] = true;

    assert(slot >= c.nextSlot);

    c.nextSlot = slot + 1;

    if (c.firstUsedSlot == -1) {
      c.firstUsedSlot = slot;
    }

    foreach (b; c.directBases) {
      allocateSlotUp(b, slot, visited);
    }

    foreach (d; c.directDerived) {
      allocateSlotDown(d, slot, visited);
    }
  }

  void allocateSlotUp(Class* c, int slot, bool[Class*] visited)
  {
    if (c in visited)
      return;

    debug(explain) {
      writef(" %s", c.name);
    }

    visited[c] = true;

    assert(slot >= c.nextSlot);

    c.nextSlot = slot + 1;

    if (c.firstUsedSlot == -1) {
      c.firstUsedSlot = slot;
    }

    foreach (d; c.directBases) {
      allocateSlotUp(d, slot, visited);
    }
  }

  static bool isMoreSpecific(Spec* a, Spec* b)
  {
    bool result = false;

    for (int i = 0; i < a.params.length; i++) {
      if (a.params[i] !is b.params[i]) {
        if (a.params[i] in b.params[i].conforming) {
          result = true;
        } else if (b.params[i] in a.params[i].conforming) {
          return false;
        }
      }
    }

    return result;
  }

  static Spec*[] best(Spec*[] candidates) {
    Spec*[] best;

    foreach (spec; candidates) {
      for (int i = 0; i != best.length; ) {
        if (isMoreSpecific(spec, best[i])) {
          best.remove(i);
          best.length -= 1;
        } else if (isMoreSpecific(best[i], spec)) {
          spec = null;
          break;
        } else {
          ++i;
        }
      }

      if (spec) {
        best ~= spec;
      }
    }

    return best;
  }

  void buildTable(Method* m, size_t dim, GroupMap[] groups, BitArray candidates)
  {
    int groupIndex = 0;

    foreach (mask, group; groups[dim]) {
      if (dim == 0) {
        auto finalMask = candidates & mask;
        Spec*[] applicable;

        foreach (i, spec; m.specs) {
          if (finalMask[i]) {
            applicable ~= spec;
          }
        }

        debug(explain) {
          writefln("%*s    dim %d group %d (%s): select best of %s",
                   (m.vp.length - dim) * 2, "",
                   dim, groupIndex,
                   group.map!(c => c.name).join(", "),
                   applicable.map!(spec => spec.toString).join(", "));
        }

        auto specs = best(applicable);

        if (specs.length > 1) {
          m.dispatchTable ~= m.info.ambiguousCallError;
        } else if (specs.empty) {
          m.dispatchTable ~= m.info.notImplementedError;
        } else {
          import std.stdio;
          m.dispatchTable ~= specs[0].info.pf;

          debug(explain) {
            writefln("%*s      %s: pf = %s",
                     (m.vp.length - dim) * 2, "",
                     specs.map!(spec => spec.toString).join(", "),
                     specs[0].info.pf);
          }
        }
      } else {
        debug(explain) {
          writefln("%*s    dim %d group %d (%s)",
                   (m.vp.length - dim) * 2, "",
                   dim, groupIndex,
                   group.map!(c => c.name).join(", "));
        }
        buildTable(m, dim - 1, groups, candidates & mask);
      }
      ++groupIndex;
    }
  }

  void findHash()
  {
    import std.random, std.math;

    void**[] vptrs;

    foreach (c; classes) {
      if (c.info.vtbl.ptr) {
        vptrs ~= c.info.vtbl.ptr;
      }
	}

    auto N = vptrs.length;

    debug(explain) {
      writefln("  finding hash factor for %s vptrs", N);
      import std.datetime;
      StopWatch sw;
      sw.start();
    }

    int M;
    auto rnd = Random(unpredictableSeed);
    ulong totalAttempts;

    for (int room = 2; room <= 6; ++room) {
      M = 1;

      while ((1 << M) < room * N / 2) {
        ++M;
      }

      hashShift = 64 - M;
      hashSize = 1 << M;
      int[] buckets;
      buckets.length = hashSize;

      debug(explain) {
        writefln("  trying with M = %s, %s buckets", M, buckets.length);
      }

      bool found;
      int attempts;

      while (!found && attempts < 100_000) {
        ++attempts;
        ++totalAttempts;
        found = true;
        hashMult = rnd.uniform!ulong | 1;
        buckets[] = 0;
        foreach (vptr; vptrs) {
          auto h = hash(vptr);
          if (buckets[h]++) {
            found = false;
            break;
          }
        }
      }

      if (found) {
        debug(explain) {
          writefln("  found %s after %s attempts and %s msecs",
                   hashMult, totalAttempts, sw.peek().msecs);
        }
        return;
      }
    }

    throw new Error("cannot find hash factor");
  }

  static auto hash(void* p) {
    return cast(uint) ((hashMult * (cast(ulong) p)) >> hashShift);
  }

  void buildTables()
  {
    foreach (m; methods) {
      debug(explain) {
        writefln("Building dispatch table for %s", *m);
      }

      auto dims = m.vp.length;
      GroupMap[] groups;
      groups.length = dims;

      foreach (int dim, vp; m.vp) {
        debug(explain) {
          writefln("  make groups for param #%s, class %s", dim, vp.name);
        }

        foreach (conforming; vp.conforming) {
          if (conforming.isClass) {
            debug(explain) {
              writefln("    specs applicable to %s", conforming.name);
            }

            BitArray mask;
            mask.length = m.specs.length;

            foreach (int specIndex, spec; m.specs) {
              if (conforming in spec.params[dim].conforming) {
                debug(explain) {
                  writefln("      %s", *spec);
                }
                mask[specIndex] = 1;
              }
            }

            debug(explain) {
              writefln("      bit mask = %s", mask);
            }

            if (mask in groups[dim]) {
              debug(explain) {
                writefln("      add class %s to existing group", conforming.name, mask);
              }
              groups[dim][mask] ~= conforming;
            } else {
              debug(explain) {
                writefln("      create new group for %s", conforming.name);
              }
              groups[dim][mask] = [ conforming ];
            }
          }
        }
      }

      int stride = 1;
      m.strides.length = dims - 1;

      foreach (int dim, vp; m.vp[1..$]) {
        debug(explain) {
          writefln("    stride for dim %s = %s", dim + 1, stride);
        }
        stride *= groups[dim].length;
        m.strides[dim] = stride;
      }

      BitArray none;
      none.length = m.specs.length;

      debug(explain) {
        writefln("    assign specs");
      }

      buildTable(m, dims - 1, groups, ~none);

      debug(explain) {
        writefln("  assign slots");
      }

      foreach (int dim, vp; m.vp) {
        debug(explain) {
          writefln("    dim %s", dim);
        }

        int i = 0;

        foreach (group; groups[dim]) {
          debug(explain) {
            writefln("      group %d (%s)",
                     i,
                     group.map!(c => c.name).join(", "));
          }
          foreach (c; group) {
            mtbls[c][m.slots[dim]].i = i;
          }

          ++i;
        }
      }

      m.firstDim = groups[0];
    }

    auto gdtblLength  = methods.filter!(m => m.vp.length > 1).map!
      (m => m.dispatchTable.length + m.slots.length + m.strides.length).sum;

    gdtbl.length = gdtblLength;
    Word* mp = gdtbl.ptr;

    debug(explain) {
      writefln("Initializing global dispatch table - %d words", gdtbl.length);
    }

    foreach (m; methods) {
      if (m.info.vp.length > 1) {
        debug(explain) {
          writefln("  %s:", *m);
          writefln("    %s: %d strides: %s", mp, m.strides.length, m.strides);
        }
        m.info.strides = mp;
        foreach (stride; m.strides) {
          mp++.i = stride;
        }
        debug(explain) {
          writefln("    %s: %d functions", mp, m.dispatchTable.length);
        }
        m.info.dispatchTable = mp;
        foreach (p; m.dispatchTable) {
          debug(explain) {
            writefln("      %s", p);
          }
          mp++.p = cast(void*) p;
        }
      }
    }

    foreach (m; methods) {
      auto slot = m.slots[0];
      if (m.info.vp.length == 1) {
        debug(explain) {
          writefln("  %s:", *m);
          writefln("    1-method, storing fp in mtbl, slot = %s", slot);
        }
        int i = 0;
        foreach (group; m.firstDim) {
          foreach (c; group) {
            Word* index = mtbls[c] + slot;
            index.p = m.dispatchTable[i];
            debug(explain) {
              writefln("      %s %s", i, index.p);
            }
          }
          ++i;
        }
      } else {
        foreach (group; m.firstDim) {
          foreach (c; group) {
            Word* index = mtbls[c] + slot;
            index.p = m.info.dispatchTable + index.i;
          }
        }
      }
      foreach (spec; m.specs) {
        auto nextSpec = findNext(spec, m.specs);
        *spec.info.nextPtr = nextSpec ? nextSpec.info.pf : null;
      }
    }
  }

  static auto findNext(Spec* spec, Spec*[] specs)
  {
    auto candidates =
      best(specs.filter!(other => isMoreSpecific(spec, other)).array);
    return candidates.length == 1 ? candidates.front : null;
  }

  void update()
  {
    seed();

    debug(explain) {
      writefln("Scooping...");
    }

	foreach (mod; ModuleInfo) {
      foreach (c; mod.localClasses) {
        scoop(c);
      }
	}

    initClasses();
    layer();
    calculateInheritanceRelationships();
    checkDeallocatorConflicts();
    allocateSlots();
    buildTables();

    needUpdate = false;
  }

  version (unittest) {
    int[] slots(alias MX)()
    {
      return methods.find!(m => m.info == &MX.ThisMethod.info)[0].slots;
    }

    Class* getClass(C)()
    {
      return classes.find!(c => c.info == C.classinfo)[0];
    }
  }
}
