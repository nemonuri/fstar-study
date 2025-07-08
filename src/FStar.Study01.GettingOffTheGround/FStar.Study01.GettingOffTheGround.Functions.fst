module FStar.Study01.GettingOffTheGround.Functions

// [Functions](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#functions)

(*
## Lambda terms

- F*는 람다식 꼴을 이용해 함수를 정의
- 예시
  - `fun (x:int) -> x + 1`
  - `fun x -> x + 1`
    - 컴파일러가 자동으로 타입을 추론
*)

(*
## Named functions

- 모든 term은 let binding을 통해 이름을 부여할 수 있다.
  - Lambda term도 마찬가지.
*)
let incr_ver1 = fun (x:int) -> x + 1 // 정석적인 방법
let incr_ver2 (x:int) = x + 1 // Lambda term 생략
let incr_ver3 x = x + 1 // Type 생략