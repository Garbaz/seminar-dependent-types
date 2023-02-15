{-# OPTIONS --type-in-type #-}

data Σ (A : Set) (B : A → Set) : Set where
    ⟨_,_⟩ : (x : A) → B x → Σ A B

[_,_] : Set → Set → Set
[ A , B ] = Σ A (λ _ → B) 

-- [_,_] : {A B : Set} → A → B → Pair A B
-- [ a , b ] = ⟨ a , b ⟩

left : {A B : Set} → [ A , B ] → A
left ⟨ a , b ⟩ = a

right : {A B : Set} → [ A , B ] → B
right ⟨ a , b ⟩ = b

well-ordered : (_≺_ : {A : Set} → A → A → Set) → Set
well-ordered _≺_ = {!   !} 



-- Choice : Set → Set
-- Choice A = A → A → A

-- left : {A : Set} → Choice A
-- left x y = x

-- right : {A : Set} → Choice A
-- right x y = y

-- if_then_else_ : {A : Set} → Choice A → A → A → A
-- if c then t else f = c t f

-- P : Set → Set → {Choice Set} → Set
-- P A B {c} = if c then A else B

-- p : {A B : Set} → A → B → {c : Choice Set} → P A B {c}
-- p {A} {B} a b {c} = {!   !}

-- cc : {A : Set} → Choice (Choice A)
-- cc x y z w = if x then (if y then z else w) else (if y then w else z)

-- q : {A : Set} → {c : Choice Set} → {! if c then A else Set    !}
-- q A = {!   !}