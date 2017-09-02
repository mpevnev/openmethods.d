// Written in the D programming language.

/++
 This module implements fast open multi-_methods.

 Open _methods are like virtual functions, except that they are free functions,
 living outside of any class. Multi-_methods can take into account the dynamic
 types of more than one argument to select the most specialized variant of the
 function.

 This implementation uses compressed dispatch tables to deliver a performance
 similar to ordinary virtual function calls, while minimizing the size of the
 dispatch tables in presence of multiple virtual arguments.

 Synopsis of openmethods:
---

import openmethods; // import lib
mixin(registerMethods); // once per module - don't forget!

interface  Animal {}
class Dog : Animal {}
class Pitbull : Dog {}
class Cat : Animal {}
class Dolphin : Animal {}

// open method with single argument <=> virtual function "from outside"
string kick(virtual!Animal);

@method // implement 'kick' for dogs
string _kick(Dog x) // note the underscore
{
  return "bark";
}

@method("kick") // use a different name for specialization
string notGoodIdea(Pitbull x)
{
  return next!kick(x) ~ " and bite"; // aka call 'super'
}

// multi-method
string meet(virtual!Animal, virtual!Animal);

// 'meet' implementations
@method
string _meet(Animal, Animal)
{
  return "ignore";
}

@method
string _meet(Dog, Dog)
{
  return "wag tail";
}

@method
string _meet(Dog, Cat)
{
  return "chase";
}

void main()
{
  updateMethods(); // once per process - don't forget!

  import std.stdio;

  Animal hector = new Pitbull, snoopy = new Dog;
  writeln("kick snoopy: ", kick(snoopy)); // bark
  writeln("kick hector: ", kick(hector)); // bark and bite

  Animal felix = new Cat, flipper = new Dolphin;
  writeln("hector meets felix: ", meet(hector, felix)); // chase
  writeln("hector meets snoopy: ", meet(hector, snoopy)); // wag tail
  writeln("hector meets flipper: ", meet(hector, flipper)); // ignore
}
---

 Copyright: Copyright Jean-Louis Leroy 2017

 License:   $(LINK2 http://boost.org/LICENSE_1_0.txt, Boost License 1.0).

 Authors:   Jean-Louis Leroy 2017
+/

module openmethods;

import std.algorithm;
import std.meta;
import std.traits;

import openmethods.runtime;

debug(explain) {
  import std.stdio;
}

debug(traceCalls) {
  import std.stdio;
}

// ============================================================================
// Pubic stuff

/++
 Mark a parameter as virtual, and declare a method.

 A new function is introduced in the current scope. It has the same name as the
 declared method; its parameter consists in the declared parameters, stripped
 from the `virtual!` qualifier. Calls to this function resolve to the most
 specific method that matches the arguments.

 The rules for determining the most specific function are exactly the same as
 those that guide the resolution of function calls in presence of overloads -
 only the resolution happens at run time, taking into account the argument's
 $(I dynamic) type. In contrast, the normal function overload resolution is a
 compile time mechanism that takes into account the $(I static) type of the
 arguments.

 Examples:
 ---
 Matrix times(double, virtual!Matrix);
 string fight(virtual!Character, virtual!Creature, virtual!Device);

 Matrix a = new DiagonalMatrix(...);
 auto result = times(2, a);

 fight(player, room.guardian, bag[item]);
 ---
 +/

class virtual(T)
{
}

/++
 Used as an attribute: add an override to a method.

 If called without argument, the function name must consist in a method name,
 prefixed with an underscore. The function is added to the method as a
 specialization.

 If called with a string argument, it is interpreted as the name of the method
 to specialize. The function name can then be any valid identifier. This is
 useful to allow one override to call a specific override without going through
 the dynamic dispatch mechanism.

 Examples:
 ---
 @method
 string _fight(Character x, Creature y, Axe z)
 {
   ...
 }

 @method("times")
 Matrix doubleTimesDiagonal(double a, immutable(DiagonalMatrix) b)
 {
   ...
 }
 ---

+/

struct method
{
  string id;
}

/++ Call the _next most specialized override if it exists. In other words, call
 the override that would have been called if this one had not been defined.

 Examples:
 ---
void inspect(virtual!Vehicle, virtual!Inspector);

@method
void _inspect(Vehicle v, Inspector i)
{
  writeln("Inspect vehicle.");
}

@method
void _inspect(Car v, Inspector i)
{
  next!inspect(v, i);
  writeln("Inspect seat belts.");
}

@method
void _inspect(Car v, StateInspector i)
{
  next!inspect(v, i);
  writeln("Check insurance.");
}

...

Vehicle car = new Car;
Inspector inspector = new StateInspector;
inspect(car, inspector); // Inspect vehicle. Inspect seat belts. Check insurance.
 ---
+/

auto next(alias F, T...)(T args)
{
  alias M = typeof(F(MethodTag.init, T.init));
  return M.nextPtr!(T)(args);
}

/++ Used as a string mixin: register the methods declaration and definitions in
 the current module.

 Examples:
 ---
import openmethods;
mixin(registerMethods);
 ---
 +/

auto registerMethods(string moduleName = __MODULE__)
{
  import std.format;
  return format("mixin(openmethods._registerMethods!%s);"
                ~ "mixin openmethods._registerSpecs!%s;\n",
                moduleName, moduleName);
}

/++
 Update the runtime dispatch tables. Must be called once before calling any method. Typically this is done at the beginning of `main`.
 +/

void updateMethods()
{
  Runtime rt;
  rt.update();
}

bool needUpdateMethods()
{
  return Runtime.needUpdate;
}

alias MethodError = openmethods.runtime.MethodError;

/++
 Information passed to the error handler function.

 +/

void defaultMethodErrorHandler(MethodError error)
{
  import std.stdio;
  import std.array;
  stderr.writefln("call to %s(%s) is %s, aborting...",
                  error.functionName,
                  error.args.map!(a => a.toString).join(", "),
                  error.reason == MethodError.NotImplemented
                  ? "not implemented" : "ambiguous");
  import core.stdc.stdlib : abort;
  abort();
}

alias MethodErrorHandler = void function(MethodError error);

MethodErrorHandler errorHandler = &defaultMethodErrorHandler;

/++
 Set the function that is called if a method cannot be called with the
 arguments. Default is to `abort` the program.
+/

void function(MethodError error)
setMethodErrorHandler(void function(MethodError error) handler)
{
  auto prev = errorHandler;
  errorHandler = handler;
  return prev;
}

// ============================================================================
// Private parts. This doesn't exist. If you believe it does and use it, on
// your head be it.

enum IsVirtual(T) = false;
enum IsVirtual(T : virtual!U, U) = true;

private alias VirtualType(T : virtual!U, U) = U;

private template VirtualArity(QP...)
{
  static if (QP.length == 0) {
    enum VirtualArity = 0;
  } else static if (IsVirtual!(QP[0])) {
    enum VirtualArity = 1 + VirtualArity!(QP[1..$]);
  } else {
    enum VirtualArity = VirtualArity!(QP[1..$]);
  }
}

private template CallParams(T...)
{
  static if (T.length == 0) {
    alias CallParams = AliasSeq!();
  } else {
    static if (IsVirtual!(T[0])) {
      alias CallParams = AliasSeq!(VirtualType!(T[0]), CallParams!(T[1..$]));
    } else {
      alias CallParams = AliasSeq!(T[0], CallParams!(T[1..$]));
    }
  }
}

private template castArgs(T...)
{
  import std.typecons : tuple;
  static if (T.length) {
    template To(S...)
    {
      auto arglist(A...)(A args) {
        alias QP = T[0];
        static if (IsVirtual!QP) {
          static if (is(VirtualType!QP == class)) {
            auto arg = cast(S[0]) cast(void*) args[0];
          } else {
            static assert(is(VirtualType!QP == interface),
                             "virtual argument must be a class or an interface");
            auto arg = cast(S[0]) args[0];
          }
        } else {
          auto arg = args[0];
        }
        return
          tuple(arg,
                castArgs!(T[1..$]).To!(S[1..$]).arglist(args[1..$]).expand);
      }
    }
  } else {
    template To(X...)
    {
      auto arglist() {
        return tuple();
      }
    }
  }
}

private immutable MptrInDeallocator = "deallocator";
private immutable MptrViaHash = "hash";

struct Method(string id, string Mptr, R, T...)
{
  alias QualParams = T;
  alias Params = CallParams!T;
  alias R function(Params) Spec;
  alias ReturnType = R;
  enum name = id;

  static __gshared MethodInfo info;

  static R notImplementedError(T...)
  {
    import std.meta;
    errorHandler(new MethodError(MethodError.NotImplemented, &info));
    static if (!is(R == void)) {
      return R.init;
    }
  }

  static R ambiguousCallError(T...)
  {
    errorHandler(new MethodError(MethodError.AmbiguousCall, &info));
    static if (!is(R == void)) {
      return R.init;
    }
  }

  static Method discriminator(MethodTag, CallParams!T);

  static if (Mptr == MptrInDeallocator) {
    static auto getMptr(T)(T arg)
    {
      static if (is(T == class)) {
        return cast(const Word*) arg.classinfo.deallocator;
      } else {
        Object o = cast(Object)
          (cast(void*) arg - (cast(Interface*) **cast(void***) arg).offset);
        return cast(const Word*) o.classinfo.deallocator;
      }
    }
  } else static if (Mptr == MptrViaHash) {
    static auto getMptr(T)(T arg) {
      static if (is(T == class)) {
        return Runtime.hashTable[Runtime.hash(*cast (void**) arg)].pw;
      } else {
        Object o = cast(Object)
          (cast(void*) arg - (cast(Interface*) **cast(void***) arg).offset);
        return Runtime.hashTable[Runtime.hash(*cast (void**) o)].pw;
      }
    }
  }

  template Indexer(Q...)
  {
    static const(Word)* move(P...)(const(Word)* slots, const(Word)* strides, P args)
    {
      alias Q0 = Q[0];
      debug(traceCalls) {
        stderr.write(" | ", Q0.stringof, ":");
      }
      static if (IsVirtual!Q0) {
        alias arg = args[0];
        const (Word)* mtbl = getMptr(arg);
        debug(traceCalls) {
          stderr.writef(" %s ", mtbl);
          stderr.writef(" %s ", slots.i);
          stderr.writef(" %s ", mtbl[slots.i].p);
        }
        return Indexer!(Q[1..$])
          .moveNext(cast(const(Word)*) mtbl[slots.i].p,
                    slots + 1,
                    strides, // stride for dim 0 is 1, not stored
                    args[1..$]);
      } else {
        return Indexer!(Q[1..$]).move(slots, strides, args[1..$]);
      }
    }

    static const(Word)* moveNext(P...)(const(Word)* dt, const(Word)* slots, const(Word)* strides, P args)
    {
      static if (Q.length > 0) {
        alias Q0 = Q[0];
        debug(traceCalls) {
          stderr.write(" | ", Q0.stringof, ":");
        }
        static if (IsVirtual!Q0) {
          alias arg = args[0];
          const (Word)* mtbl = getMptr(arg);
          debug(traceCalls) {
            stderr.writef(" %s, %s, %s", mtbl, slots.i, mtbl[slots.i].p);
          }
          return Indexer!(Q[1..$])
            .moveNext(dt + mtbl[slots.i].i * strides.i,
                      slots + 1,
                      strides + 1,
                      args[1..$]);
        } else {
          return Indexer!(Q[1..$]).moveNext(dt, slots, strides, args[1..$]);
        }
      } else {
        return dt;
      }
    }

    static const(Word)* unary(P...)(P args)
    {
      alias Q0 = Q[0];
      debug(traceCalls) {
        stderr.write(" | ", Q0.stringof, ":");
      }
      static if (IsVirtual!Q0) {
        return getMptr(args[0]);
      } else {
        return Indexer!(Q[1..$]).unary(args[1..$]);
      }
    }
  }

  static auto dispatcher(CallParams!T args)
  {
    debug(traceCalls) {
      stderr.write(info.name);
    }

    assert(info.vp.length == 1 || info.dispatchTable, "updateMethods not called");
    assert(info.vp.length == 1 || info.slots);
    assert(info.vp.length == 1 || info.strides);

    static if (VirtualArity!QualParams == 1) {
      debug(traceCalls) {
        stderr.writef("%s %s", Indexer!(QualParams).unary(args), info.slots[0].i);
      }
      auto pf = cast(Spec) Indexer!(QualParams).unary(args)[info.slots[0].i].p;
    } else {
      auto pf =
        cast(Spec) Indexer!(QualParams).move(info.slots, info.strides, args).p;
    }

    debug(traceCalls) {
      writefln(" pf = %s", pf);
    }

    assert(pf);

    static if (is(R == void)) {
      pf(args);
    } else {
      return pf(args);
    }
  }

  shared static this() {
    info.name = id;

    static if (Mptr == MptrInDeallocator) {
      ++Runtime.methodsUsingDeallocator;
    } else static if (Mptr == MptrViaHash) {
      ++Runtime.methodsUsingHash;
    }

    info.ambiguousCallError = &ambiguousCallError;
    info.notImplementedError = &notImplementedError;

    foreach (QP; QualParams) {
      int i = 0;
      static if (IsVirtual!QP) {
        info.vp ~= VirtualType!(QP).classinfo;
      }
    }

    debug(explain) {
      writefln("registering %s", info);
    }

    Runtime.methodInfos[&info] = &info;
    Runtime.needUpdate = true;
  }

  shared static ~this() {
    debug(explain) {
      writefln("Unregistering %s", info);
    }

    Runtime.methodInfos.remove(&info);
    Runtime.needUpdate = true;
  }

  static struct Specialization(alias fun)
  {
    alias Parameters!fun SpecParams;

    static __gshared SpecInfo si;

    static wrapper = function ReturnType(Params args) {
      static if (is(ReturnType == void)) {
        fun(castArgs!(T).To!(SpecParams).arglist(args).expand);
      } else {
        return fun(castArgs!(T).To!(SpecParams).arglist(args).expand);
      }
    };
  }

  static Spec nextPtr(T...) = null;
}

struct MethodTag { }

private immutable bool hasVirtualParameters(alias F) = anySatisfy!(IsVirtual, Parameters!F);

unittest
{
  void meth(virtual!Object);
  static assert(hasVirtualParameters!meth);
  void nonmeth(Object);
  static assert(!hasVirtualParameters!nonmeth);
}

struct mptr
{
  string index;
}

string _registerMethods(alias MODULE)()
{
  import std.array;
  import std.format;
  string[] code;
  foreach (m; __traits(allMembers, MODULE)) {
    static if (is(typeof(__traits(getOverloads, MODULE, m)))) {
      foreach (o; __traits(getOverloads, MODULE, m)) {
        static if (hasVirtualParameters!o) {
          static if (hasUDA!(o, openmethods.mptr)) {
            static assert(getUDAs!(o, openmethods.mptr).length == 1,
                          "only une @mptr allowed");
            immutable index = getUDAs!(o, openmethods.mptr)[0].index;
          } else {
            immutable index = "deallocator";
          }
          auto meth =
            format(`openmethods.Method!("%s", "%s", %s, %s)`,
                   m,
                   index,
                   ReturnType!o.stringof,
                   Parameters!o.stringof[1..$-1]);
          code ~= format(`alias %s = %s.dispatcher;`, m, meth);
          code ~= format(`alias %s = %s.discriminator;`, m, meth);
        }
      }
    }
  }
  return join(code, "\n");
}

mixin template _registerSpecs(alias MODULE)
{
  import openmethods.runtime;
  mixin template wrap(M, S)
  {
    static struct Register {

      static __gshared openmethods.runtime.SpecInfo si;

      shared static this() {
        si.pf = cast(void*) S.wrapper;

        debug(explain) {
          import std.stdio;
          writefln("Registering override %s%s", M.name, S.SpecParams.stringof);
        }

        foreach (i, QP; M.QualParams) {
          static if (openmethods.IsVirtual!QP) {
            si.vp ~= S.SpecParams[i].classinfo;
          }
        }

        M.info.specInfos ~= &si;
        si.nextPtr = cast(void**) &M.nextPtr!(S.SpecParams);

        Runtime.needUpdate = true;
      }

      shared static ~this()
      {
        debug(explain) {
          import std.stdio;
          writefln("Removing override %s%s", M.name, S.SpecParams.stringof);
        }

        import std.algorithm, std.array;
        M.info.specInfos = M.info.specInfos.filter!(p => p != &si).array;
        Runtime.needUpdate = true;
      }
    }

    __gshared Register r;
  }

  import std.traits;

  shared static this()
  {
    foreach (_openmethods_m_; __traits(allMembers, MODULE)) {
      static if (is(typeof(__traits(getOverloads, MODULE, _openmethods_m_)))) {
        foreach (_openmethods_o_; __traits(getOverloads, MODULE, _openmethods_m_)) {
          static if (hasUDA!(_openmethods_o_, openmethods.method)) {
            version (GNU) {
              immutable _openmethods_id_ = _openmethods_m_[1..$];
            } else {
              static if (is(typeof(getUDAs!(_openmethods_o_, openmethods.method)[0]) == openmethods.method)) {
                immutable _openmethods_id_ = getUDAs!(_openmethods_o_, openmethods.method)[0].id;
              } else {
                static assert(_openmethods_m_[0] == '_',
                              m ~ ": method name must begin with an underscore, "
                              ~ "or be set in @method()");
                immutable _openmethods_id_ = _openmethods_m_[1..$];
              }
            }
            alias M = typeof(mixin(_openmethods_id_)(openmethods.MethodTag.init, Parameters!(_openmethods_o_).init));
            mixin wrap!(M, M.Specialization!(_openmethods_o_));
          }
        }
      }
    }
  }

  shared static ~this()
  {
    debug(explain) {
      import std.stdio;
      writefln("Unregistering specs from %s", MODULE.stringof);
    }
  }
}
