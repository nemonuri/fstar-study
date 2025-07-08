module FStar.Study01.GettingOffTheGround.BooleanRefinementType

// # [Boolean refinement types](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#boolean-refinement-types)

(*
## Boolean refinement type 이란?

- refinement type 을 한국어로 번역하면, '개량 타입'
- `x:t { e }` 꼴
  - t는 타입
  - e는 x를 자유 변수로 가진 `t → bool` 함수
    - bool 타입 상수일 수도 있음
  - 집합 `{ x∈t | e(x) }` 과 외연적으로 같음
*)
let nat = x:int{x >= 0}

let empty = x:int { false } //the empty set
let zero = x:int{ x = 0 } //the type containing one element `0`
let pos = x:int { x > 0 } //the positive numbers
let neg = x:int { x < 0 } //the negative numbers
let even = x:int { x % 2 = 0 } //the even numbers
let odd = x:int { x % 2 = 1 } //the odd numbers

(*
## [Refinement subtyping](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#basic-syntactic-structure)
*)

(*
## Refinement subtyping

객체 지형 언어의 'Type Casting'과 비슷한 개념

1. *eliminating* a refinement type

- = 개량 타입 제거
- `e:( x:t{ p } ) ⊢ e:t`

2. *introducing* a refinement type

- = 개량 타입 도입
- `e:t , p[x := e] ⊢ e:( x:t{ p } )`
- F* 컴파일러는 `p[x := e]`의 진리값을 판단하기 위해 SMT solver를 사용한다.
*)

(*
## An example

(TODO)
*)
let v1:even = 2
let v2:odd = v1 + 1 // 이 코드 한 줄을 추가하니, SMT Query가 발생한다.