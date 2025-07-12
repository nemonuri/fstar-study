module InductiveTypeDefinitions.StrictlyPositiveDefinitions

noeq
type free (f:([@@@ strictly_positive] _:Type -> Type))
          (a:Type) 
  : Type =
  | Leaf : a -> free f a
  | Branch : f (free f a) -> free f a

let binary_tree (a:Type) = free (fun t -> t & t) a
let list_redef ([@@@strictly_positive] a:Type) = list a
let variable_branching_list a = free list_redef a
let infinite_branching_tree a = free (fun t -> nat -> t) a