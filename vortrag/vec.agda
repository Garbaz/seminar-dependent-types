import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_) 

data Vec : Set -> ℕ -> Set where
    nil : {a : Set} -> Vec a 0
    _::_ : {a : Set} -> {n : ℕ} -> a -> Vec a n -> Vec a (1 + n)

append : {a : Set} -> {n m : ℕ} -> Vec a n -> Vec a m -> Vec a (n + m)
append nil v' = v'
append (x :: v) v' = x :: (append v v')

head : {a : Set} -> {n : ℕ} -> {1 ≤ n} -> Vec a n -> a
head (x :: v) = x