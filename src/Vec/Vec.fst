// For more information see http://www.fstar-lang.org/tutorial/
module Vec

type even (a:Type) =
 | ENil : even a
 | ECons : a -> odd a -> even a
and odd (a:Type) =
 | OCons : a -> even a -> odd a