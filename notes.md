Motivation
==========

When reasoning within one state it is often helpful to have tools from
functional programming. Map and filter can already be expressed, fold / reduce
is defined for different use cases in multiple locations. The semantics of
evaluating these fold operators is different: e.g. ReduceSet defines an arbitrary ordering
of the input set (where it's not always clear if any ordering is permissible) while Reduce has an extra parameter fun that
defines an ordering that prevents reasoning on all subsets. By making assumptions
on the arguments or the level of the operator we could use an efficient
specialized implementations for these cases in a back-end while keeping
the definitions all in terms of one fold operator.

Current versions of fold / reduce
=================================

* Reduce: defined in specifications/ewd998/Utils.tla
          in repository [Examples](https://github.com/tlaplus/Examples)
* ReduceSet: defined in modules/FiniteSetsExt.tla
          in repository [CommunityModules](https://github.com/tlaplus/CommunityModules)
* ReduceSeq: defined in modules/SequencesExt.tla
          in repository [CommunityModules](https://github.com/tlaplus/CommunityModules)

Fold vs reduce: in functional convention, reduce is a special case of fold where 
    the base case is already known. E.g. reduce f list = fold f u list where u
    is the unit element regarding f. The definition of Reduce from ewd998 is
    unusual because it has a base element - on the other hand the operator is
    undefined if from > to, such that the smallest defined value of Reduce applies
    op once.

Constness of the operator
========================

There is no restriction on the level of the operator applied during folding.
Many operators (e.g. summing up counters in EWD998) are constant which makes
them much easier to evaluate. This would not prevent the application of the fold
to state or actions level expressions but it would ensure that the level of the
input does not change. We believe this is a reasnable assumption to make.

TODO: find counterexample (recursion that produces x' # 0 /\ ... /\ x' # n ?)

