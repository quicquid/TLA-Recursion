----------------------------- MODULE Recursion -----------------------------

EXTENDS Naturals, FiniteSets 

(* Operators that were previously defined in various places *)

(* This operator is originally defined at:

   https://github.com/tlaplus/Examples/blob/d5740ed41ff403927552255113a6c91f716660c8/specifications/ewd998/Utils.tla#L7
 *)  
LOCAL Reduce(op(_,_), fun, from, to, base) == 
(**************************************************************************)
(* Reduce the elements in the range from..to of the function's co-domain. *)
(**************************************************************************)
  LET reduced[i \in from..to] ==
    IF i = from THEN op(base, fun[i])
    ELSE op(reduced[i - 1], fun[i])
    IN reduced[to]


(* This operator is originally defined at:

   https://github.com/tlaplus/CommunityModules/blob/a39cb8af01febb10a227e2f5adb9264a2f394c7e/modules/FiniteSetsExt.tla#L7
 *)  
LOCAL ReduceSet(op(_, _), set, acc) ==
  (***************************************************************************)
  (* TLA+ forbids recursive higher-order operators, but it is fine with      *)
  (* recursive functions.  ReduceSet generates a recursive function over the *)
  (* subsets of a set, which can be used to recursively run a defined        *)
  (* operator.  This can then be used to define other recursive operators.   *)
  (* The op is assumed to be an abelian/commutative operation.               *)
  (***************************************************************************)
  LET f[s \in SUBSET set] ==
    IF s = {} THEN acc
    ELSE LET x == CHOOSE x \in s: TRUE
         IN op(x, f[s \ {x}])
  IN f[set]


(* This operator is originally defined at:

   https://github.com/tlaplus/CommunityModules/blob/a39cb8af01febb10a227e2f5adb9264a2f394c7e/modules/SequencesExt.tla#L170
 *)  
LOCAL ReduceSeq(op(_, _), seq, acc) == 
  (***************************************************************************)
  (* We can't just apply ReduceSet to the Range(seq) because the same        *)
  (* element might appear twice in the sequence.                             *)
  (***************************************************************************)
  ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)


(*
   New operator definitions that we are proposing. They can be defined
   in terms of the above-defined Reduce and ReduceSet. However, the interface
   of our operators is more common in functional programming languages.

   Importantly, we would require the parameter operator `op` to be
   constant-level or state-level, that is, forbid side effects that are
   caused by primes.
   *)

(*
   Intuitive semantics:

   Initialize a temporary variable `accum` with the value of `base`.  Iterate
   over the elements of `DOMAIN fun` in a deterministic but unknown order,
   update the value of `accum` to the value of `op(accum, f[x]`), where `x` is
   the current value of the iterator. The result of `FoldFun` is the computed
   value of `accum`.
 *)
FoldFun(op(_,_), base, fun) == 
  (*
    This is an implementation in terms of previously defined operators.
    A tool is free to define its own, more efficient, implementation.
   *) 
  Reduce(op, fun, 1, Cardinality(DOMAIN fun), base) 

(*
   Intuitive semantics:

   Initialize a temporary variable `accum` with the value of `base`.  Iterate
   over the elements in set in a deterministic but unknown order, update the
   value of `accum` to the value of `op(accum, x`), where `x` is the current
   value of the iterator. The result of `FoldSet` is the computed value of
   `accum`.
 *)  
FoldSet(op(_,_), base, set) ==
  (*
    This is an implementation in terms of previously defined operators.
    A tool is free to define its own, more efficient, implementation.
   *) 
  ReduceSet(op, set, base)

(* Use cases *)
  
\* fake state to evaluate expression
VARIABLE X
Init == X = 0
Next == UNCHANGED X

BigSet == FoldFun(LAMBDA x, y: x \cup y, {}, {})

Test1 == FoldSet(LAMBDA x, y: x \cup y, {}, {{1,2,3}, {2,3,4}, {4,5,6}}) \* set flattening
Test2 == FoldSet(LAMBDA x, y: x /\ y, TRUE, {TRUE, FALSE,TRUE}) \* propositional clause evaluation
Test3 == FoldSet(LAMBDA x, y: x \ y, {}, {{1,2,3}, {2,3,4}, {4,5,6}}) \* set difference -- is this well defined? suppose choose picks {4,5,6} first, we should get {6}, if we shoose {1,2,3} first we chould get {1}
Test4 == FoldSet(LAMBDA x, y: x \ y, {}, {{4,5,6}, {2,1,3}, {2,3,4}}) \* set difference -- is this well defined? suppose choose picks {4,5,6} first, we should get {6}, if we shoose {1,2,3} first we chould get {1}
Test5 == Test3 = Test4 \* surprised this works
Test6 == FoldSet(LAMBDA x, y: X' # x /\ y, X' # 0, {1, 2}) \* creating an action by recursion -- outside of the target set

(* a probably most common use case for fold: summing up the arguments *)
Test7 == FoldSet(LAMBDA x, y: x + y, 0, 1..10)

AllTests == /\ Test1 = {1,2,3,4,5, 6}
            /\ ~Test2
            /\ Test5
            /\ Test6 = 55



=============================================================================
\* Modification History
\* Last modified Tue Feb 02 16:52:38 CET 2021 by marty
\* Created Tue Jan 26 11:26:58 CET 2021 by marty

