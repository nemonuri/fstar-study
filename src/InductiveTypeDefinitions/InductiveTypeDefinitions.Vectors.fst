module InductiveTypeDefinitions.Vectors

type list2 (a:Type) =
  | Nil2 : list2 a
  | Cons2 : hd:a -> tl:list2 a -> list2 a

type vec (a:Type) : nat -> Type =
  | Nil : vec a 0
  | Cons : #n:nat -> hd:a -> tl:vec a n -> vec a (n + 1)
