import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_) 

data Vec (A : Set) : ℕ -> Set where
    nil  : Vec A 0
    _::_ : {n : ℕ} -> (a : A) -> Vec A n -> Vec A (1 + n)

append : {A : Set} -> {n m : ℕ} -> Vec A n -> Vec A m -> Vec A (n + m)
append nil v' = v'
append (x :: v) v' = x :: (append v v')

head : {A : Set} -> {n : ℕ} -> {1 ≤ n} -> Vec A n -> A
head (x :: v) = x 