module Part4.Pure.ImperativeLanguage

open FStar.Classical.Sugar

let var = nat

type expr =
  | EConst : int -> expr                           // constants: ..., -1, 0, 1, ...
  | EVar   : var -> expr                           // global variables
  | EAdd   : expr -> expr -> expr                  // arithmetic: e1 + e2
  
type program = 
  | Assign : var -> expr -> program                // x := e
  | Seq    : program -> program -> program         // p1; p2
  | If     : expr -> program -> program -> program // if e then p1 else p2
  | Repeat : expr -> program -> program            // repeat n { p }

// The state of a program is a map from global variable to integers
let state = var -> int
let read (s:state) (i:var) : int = s i
let write (s:state) (i:var) (v:int)
  : state
  = fun j -> if i=j then v else read s j


let rec eval_expr (e:expr) (s:state)
  : int
  = match e with
    | EConst v ->
      v
      
    | EVar x ->
      read s x
      
    | EAdd e1 e2 ->
      eval_expr e1 s + eval_expr e2 s


let st (a:Type) = state -> (a & state)

let get : st state = fun s -> (s, s)

let put (s:state) : st unit = fun _ -> ((), s)

let (let!) #a #b (f:st a) (g: a -> st b) : st b = 
  fun s -> let v, s' = f s in g v s'

let return #a (x:a) : st a = fun s -> (x, s)


let rec run (p:program)
  : Tot (st unit)
        (decreases %[p;0])
  = match p with
    | Assign x e -> 
      let! s = get in
      let v = eval_expr e s in
      put (write s x v)

    | Seq p1 p2 -> 
      run p1;!
      run p2

    | If e p1 p2 ->
      let! s = get in
      let n = eval_expr e s in
      if n <> 0 then run p1 else run p2
      
    | Repeat e p ->
      let! s = get in
      let n = eval_expr e s in
      if n <= 0 then return ()
      else run_repeat p n

and run_repeat (p:program) (n:nat)
  : Tot (st unit)
        (decreases %[p; 1; n])
  = if n = 0 then return ()
    else ( run p ;! run_repeat p (n - 1) )


let triple (pre:state -> prop)
           (c:program)
           (post:state -> prop)
  = forall s0. pre s0 ==> post (snd (run c s0))

let assignment (x:var) (e:expr) (post:state -> prop)
  : Lemma (triple (fun s0 -> post (write s0 x (eval_expr e s0)))
                  (Assign x e)
                  post)
  = ()

let sequence (p1 p2:program)
             (pre pre_mid post:state -> prop)
  : Lemma 
    (requires 
      triple pre p1 pre_mid /\
      triple pre_mid p2 post)
    (ensures
      triple pre (Seq p1 p2) post)
  = ()

let conditional (e:expr)
                (p1 p2:program)
                (pre post:state -> prop)
  : Lemma 
    (requires 
      triple (fun s -> pre s /\ eval_expr e s =!= 0) p1 post /\
      triple (fun s -> pre s /\ eval_expr e s == 0)  p2 post)
    (ensures
      triple pre (If e p1 p2) post)
  = ()

// We need an auxilary lemma to prove it by induction for repeat_n
let rec repeat_n (p:program) (inv:state -> prop) (n:nat)
  : Lemma
    (requires triple inv p inv)
    (ensures (forall s0. inv s0 ==> inv (snd (run_repeat p n s0))))
 = if n = 0 then ()
   else repeat_n p inv (n - 1)

// Then, we use that auxiliary lemma to prove the main
// rule for reasoning about repeat using an invariant
let repeat (e:expr) (p:program) (inv:state -> prop)
  : Lemma
    (requires triple inv p inv)
    (ensures triple inv (Repeat e p) inv)
  = introduce forall s0. inv s0 ==> inv (snd (run (Repeat e p) s0)) with
    introduce _ ==> _  with
      inv_s0 . (
        let n = eval_expr e s0 in
        if n <= 0 then ()
        else repeat_n p inv n
    )

let consequence (p:program) (pre pre' post post':state -> prop)
  : Lemma
    (requires 
      triple pre p post /\
      (forall s. pre' s ==> pre s) /\
      (forall s. post s ==> post' s))
    (ensures
      triple pre' p post')
  = ()

let rec wp (c:program) (post: state -> prop) 
  : state -> prop 
  = match c with
    | Assign x e -> 
      fun s0 -> post (write s0 x (eval_expr e s0))
      
    | Seq p1 p2 ->
      wp p1 (wp p2 post)

    | If e p1 p2 -> 
      fun s0 -> 
        (eval_expr e s0 =!= 0 ==> wp p1 post s0) /\
        (eval_expr e s0 == 0  ==> wp p2 post s0)
      
    | Repeat e p ->
      fun s0 ->
        (exists (inv:state -> prop). 
          inv s0 /\
          (forall s. inv s ==> post s) /\
          (forall s. inv s ==> wp p inv s))

let rec wp_soundness (p:program) (post:state -> prop)
  : Lemma (triple (wp p post) p post)
  = match p with
    | Assign x e -> ()
    | Seq p1 p2 ->
      wp_soundness p2 post;
      wp_soundness p1 (wp p2 post)
    | If e p1 p2 ->
      wp_soundness p1 post;
      wp_soundness p2 post
    | Repeat e p ->
      introduce forall s0. wp (Repeat e p) post s0 ==> 
                      post (snd (run (Repeat e p) s0)) with
      introduce _ ==> _ with
        _ . ( 
          eliminate exists (inv:state -> prop).
                            inv s0 /\                      
                            (forall s. inv s ==> post s) /\
                            (forall s. inv s ==> wp p inv s)
          returns _
          with inv_props. (
            wp_soundness p inv;
            repeat e p inv
          )
      )

[@@"opaque_to_smt"]
let hoare p c q = triple p c q

let wp_hoare (p:program) (post:state -> prop)
  : squash (hoare (wp p post) p post)
  = reveal_opaque (`%hoare) hoare;
    wp_soundness p post

let hoare_consequence (#p:program)
                     (#pre #post:state -> prop)
                     (pre_annot:state -> prop)
                     (_: squash (hoare pre p post))
                     (_: squash (forall s. pre_annot s ==> pre s))
  : squash (hoare pre_annot p post)
  = reveal_opaque (`%hoare) hoare

let ( := ) (x:var) (y:expr) = Assign x y

let add (e1 e2:expr) = EAdd e1 e2

let c (i:int) : expr = EConst i

let v (x:var) : expr = EVar x

let rec prog (p:list program { Cons? p }) 
  : program 
  = match p with
    | [c] -> c
    | c::cs -> Seq c (prog cs)

let x = 0
let y = 1
let z = 2

let swap = prog [ z := v x; x := v y; y := v z]
let proof_swap (lx ly:int)
  : squash (hoare (fun s -> read s x = lx /\ read s y = ly) swap
                  (fun s -> read s x = ly /\ read s y = lx))
  = hoare_consequence _ (wp_hoare swap _) ()

(* 
  The PURE Effect: A Dijkstra Monad for Pure Computations 
  ...이 부분부터는, 전혀 이해 못 하겠어...!
  Lemma 가 사실 이 Pure effect 를 기반으로 구현된 거라고?
*)