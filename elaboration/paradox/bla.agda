{-# OPTIONS --type-in-type #-}

Null : Set
Null = (A : Set) → A

not : Set → Set 
not A = A → Null

Unit : Set → Set
Unit A = A → A

unit : {A : Set} → Unit A
unit = λ x → x

Bool : Set → Set
Bool A = A → A → A

true : {A : Set} → Bool A
true x y = x

false : {A : Set} → Bool A
false x y = y

_≡_ : {A : Set} → (x : A) → (y : A) → Set
_≡_ {A} x y = (P : A → Set) → P x → P y

_ : {A : Set} → true {A} ≡ true {A}
_ = λ P x → x

_≢_ : {A : Set} → (x : A) → (y : A) → Set
x ≢ y = not (x ≡ y)

q : true ≡ false → Null
q f = {!   !}

_ : {A : Set} → true {A} ≢ false {A}
_ = λ f B → {!   !}

