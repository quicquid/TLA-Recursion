----------------------------- MODULE Recursion -----------------------------

EXTENDS Naturals, FiniteSets 

LOCAL Reduce(op(_,_), fun, from, to, base) == 
(**************************************************************************)
(* Reduce the elements in the range from..to of the function's co-domain. *)
(**************************************************************************)
  LET reduced[i \in from..to] ==
    IF i = from THEN op(base, fun[i])
    ELSE op(reduced[i - 1], fun[i])
    IN reduced[to]


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


LOCAL ReduceSeq(op(_, _), seq, acc) == 
  (***************************************************************************)
  (* We can't just apply ReduceSet to the Range(seq) because the same        *)
  (* element might appear twice in the sequence.                             *)
  (***************************************************************************)
  ReduceSet(LAMBDA i, a: op(seq[i], a), DOMAIN seq, acc)


FoldFun(op(_,_), base, fun) == 
  Reduce(op, fun, 1, Cardinality(DOMAIN fun), base) 

FoldSet(op(_,_), base, set) ==
  ReduceSet(op, set, base) 



=============================================================================
\* Modification History
\* Last modified Tue Jan 26 13:00:44 CET 2021 by marty
\* Created Tue Jan 26 11:26:58 CET 2021 by marty
