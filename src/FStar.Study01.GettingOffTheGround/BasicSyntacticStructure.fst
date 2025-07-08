module BasicSyntacticStructure

// # [Basic syntactic structure](https://fstar-lang.org/tutorial/book/part1/part1_getting_off_the_ground.html#basic-syntactic-structure)

(*
## Signatures ascribe a type to a definition
- 타입 시그니쳐(signature)를 정의
- 구체적인 정의가 아닌, 시그니쳐만 정의하는 것

> **사담**
> - [ascribe (something) to](https://english.dict.naver.com/english-dictionary/#/entry/enen/d4296ae565ee411c8e2b5a70c4a816da)
*)

(*
### 오류 유형 1

```fstar
val defined_type1 : int
```

```
- BasicSyntacticStructure.defined_type1
  is declared but no definition was found
- Add an 'assume' if this is intentional
```

- 구체적인 정의를 안 하면, 이렇게 오류가 발생한다.
*)
val defined_type1 : unit

(*
- recursive definitions 
  - = let bindings
  - 타입의 재귀(recursive)적 정의
  - '할당되는 타입' ∈ '시그니쳐_타입'

> **사담**
> - 원문은 'possibly recursive definitions' 이지만, possibly 를 뺐다. 그게 나에겐 의미가 더 직관적이라서.
*)
let defined_type1 = ()

(*
- inductive type definitions
  - = datatypes
  - 타입의 귀납(inductive)적 정의
  - 다음 형태를 한, **타입 생성자 정의식**이 반복된다.
    - | *'타입 생성자 식별자'* : *'타입 생성자 시그니쳐'*
      - 타입 생성자 식별자는 반드시 대문자로 시작한다.
  - 타입 생성자 정의식이 둘 이상이면, SMT Query가 발생한다.

> **사담**
> - 엄밀히 말하면, 귀납이 아닌 연역적 정의다.
> - '수학적 귀납법'에서 이름을 따 온건가?
*)
type defined_type2 = | D1 : defined_type2 | D2 : unit -> defined_type2