// For more information see http://www.fstar-lang.org/tutorial/
module Part2.WellFounded

let binrel a = a -> a -> Type

(*
- short for “accessible”
- `r x1 x0` is provable when `x1 < x0`

타입 'acc r x0' 은, 'r x1 x0'이 맞다는 증명이 도출되는 모든 x1에 대해, 타입 'acc r x1' 생성기 멤버 'access_smaller'를 가진다.
*)
noeq
type acc (#a:Type) (r:binrel a) (x0:a) : Type =
  | AccIntro : access_smaller:(x1:a -> r x1 x0 -> acc r x1) -> acc r x0


let well_founded (#a:Type) (r:binrel a) = x:a -> acc r x
let is_well_founded (#a:Type) (r:binrel a) = forall x. squash (acc r x)


let rec fix_F (#aa:Type)
              (#r:binrel aa)
              (#p:(aa -> Type))
              (f: (x:aa -> (y:aa -> r y x -> p y) -> p x))              
              (x0:aa)
              (accessible_x0:acc r x0)
  : Tot (p x0) (decreases accessible_x0)
  = f x0 (fun y r_yx -> fix_F f y (accessible_x0.access_smaller y r_yx))

let fix (#aa:Type) (#r:binrel aa) (rwf:well_founded r)
        (p:aa -> Type) (f:(x:aa -> (y:aa -> r y x -> p y) -> p x))
        (x:aa)
  : p x
  = fix_F f x (rwf x)


let lt_nat (x y:nat) : Type = x < y == true

(* 이것의 terminate 가 증명되면, lt_nat 가 well-founded relation 이라는 것이 증명된다. *)
let rec wf_lt_nat (x:nat)
  : acc lt_nat x
  = AccIntro (fun y lt_nat -> wf_lt_nat y)

(* wf_lt_nat 의 타입은, well_founded lt_nat 이다. *)
let well_founded_lt_nat : well_founded lt_nat = wf_lt_nat

(*
Definitions of inner let-rec aux and its enclosing top-level letbinding are
not encoded to the solver, you will only be able to reason with their types

이건 무슨 경고지?
*)
let subrel_wf (#a:Type) (#r #sub_r:binrel a)
              (sub_w:(x:a -> y:a -> sub_r x y -> r x y))
              (r_wf:well_founded r)
  : well_founded sub_r
  = let rec aux (x:a)
                (acc_r:acc r x)
      : Tot (acc sub_r x) (decreases acc_r)
      = AccIntro 
          (fun y sub_r_y_x ->
             aux y (acc_r.access_smaller y (sub_w y x sub_r_y_x)))
    in
    fun x -> aux x (r_wf x)


let inverse_image (#a #b:Type) (r_b:binrel b) (f:a -> b) : binrel a =
  fun x y -> r_b (f x) (f y)

let inverse_image_wf (#a #b:Type) (#r_b:binrel b)
                     (f:a -> b)
                     (r_b_wf:well_founded r_b)
  : well_founded (inverse_image r_b f)
  = let rec aux (x:a)
                (acc_r_b:acc r_b (f x))
      : Tot (acc (inverse_image r_b f) x)
            (decreases acc_r_b)
      = AccIntro (fun y p -> aux y (acc_r_b.access_smaller (f y) p)) in
    fun x -> aux x (r_b_wf (f x))

let neg = x:int { x <= 0 }
let negate (x:neg) : nat = -x
let gt_neg : binrel neg = inverse_image lt_nat negate
let wf_gt_neg = inverse_image_wf negate wf_lt_nat


noeq
type lexicographic_order (#a:Type)
                         (#b:a -> Type)
                         (r_a:binrel a)
                         (r_b:(x:a -> binrel (b x)))
  : (x:a & b x) -> (x:a & b x) -> Type =
  | Left_lex:
    x1:a -> x2:a ->
    y1:b x1 -> y2:b x2 ->
    r_a x1 x2 ->
    lexicographic_order r_a r_b (| x1, y1 |) (| x2, y2 |)

  | Right_lex:
    x:a ->
    y1:b x -> y2:b x ->
    r_b x y1 y2 ->
    lexicographic_order r_a r_b (| x, y1 |) (| x, y2 |)

(*
...아니, 그래서, '<<' 가 low level 에서 의미하는 바가 뭔데?!??
*)

assume
val lexicographic_order_wf (#a:Type) (#b:a -> Type)
                           (#r_a:binrel a)
                           (#r_b:(x:a -> binrel (b x)))
                           (wf_a:well_founded r_a)
                           (wf_b:(x:a -> well_founded (r_b x)))
  : well_founded (lexicographic_order r_a r_b)


//A type abbreviation for a pair of nats
//  we're using dependent pairs, even though there's no real dependence here
let nat_pair = (x:nat & nat)

//Making a lexicographic ordering from a pair of nat ordering
let lex_order_nat_pair 
  : binrel nat_pair
  = lexicographic_order lt_nat (fun _ -> lt_nat)

// The lex order on nat pairs is well-founded, using our general proof
// of lexicographic composition of well-founded orders
let lex_order_nat_pair_wf 
  : well_founded lex_order_nat_pair
  = lexicographic_order_wf wf_lt_nat (fun _ -> wf_lt_nat)

// A utility to introduce lt_nat
let mk_lt_nat (x:nat) (y:nat { x < y }) 
  : lt_nat x y
  = let _ : equals (x < y) true = Refl in
    ()
    
// A utility to make a lex ordering of nat pairs
let mk_lex_order_nat_pair (xy0:nat_pair) 
                          (xy1:nat_pair {
                            let (|x0, y0|) = xy0 in
                            let (|x1, y1|) = xy1 in
                            x0 < x1 \/ (x0 == x1 /\ y0 < y1)
                          })
  : lex_order_nat_pair xy0 xy1
  = let (|x0, y0|) = xy0 in
    let (|x1, y1|) = xy1 in
    if x0 < x1 then Left_lex x0 x1 y0 y1 (mk_lt_nat x0 x1)
    else Right_lex x0 y0 y1 (mk_lt_nat y0 y1)

// Defining ackermann, where `arec` is called for recursive calls
// on pairs that precede xy, lexicographically
let ackermann' (xy: nat_pair)
               (arec: (xy':nat_pair -> lex_order_nat_pair xy' xy -> nat))
  : nat
  = let (| x, y |) = xy in
    if x = 0 then y + 1
    else if y = 0 then arec (| x - 1, 1 |) (mk_lex_order_nat_pair _ _)
    else arec (| x - 1, arec (| x, y - 1|) (mk_lex_order_nat_pair _ _) |)
              (mk_lex_order_nat_pair _ _)

// Tie the knot with `fix`
let ackermann : nat_pair -> nat = fix lex_order_nat_pair_wf (fun _ -> nat) ackermann'