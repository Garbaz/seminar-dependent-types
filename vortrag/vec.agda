import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; cong; sym)
open Eq using (_≡_)
-- open import Data.Nat using (ℕ; zero; suc; _+_; _≤_) 

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

data _==_ : Nat -> Nat -> Set where
  refl : {x : Nat} -> x == x

_+_ : Nat -> Nat -> Nat
zero + y = y
(suc x) + y = suc (x + y)

cong : {x y : Nat} -> x == y -> (suc x) == (suc y)
cong refl = refl

assoc : (x : Nat) -> (y : Nat) -> (z : Nat) -> ((x + y) + z) == (x + (y + z))
assoc zero    y z = refl
assoc (suc x) y z = cong (assoc x y z)

data Vec : Set -> Nat -> Set where
    nil  : {A : Set} -> Vec A zero
    _::_ : {A : Set} -> {n : Nat} -> (a : A) -> Vec A n -> Vec A (suc n)

append : {A : Set} -> {n m : Nat} -> Vec A n -> Vec A m -> Vec A (n + m)
append nil      v' = v'
append (x :: v) v' = x :: (append v v')

head : {A : Set} -> {n : Nat} -> Vec A (suc n) -> A
head (x :: v) = x