{-# OPTIONS --type-in-type #-}

℘ : Set → Set
℘ A = A → Set

U : Set
U = {A : Set} → (℘ A → A) → A

τ : ℘ U → U
τ pU pA→A = pA→A (λ a → {!   !})

σ : U → ℘ U
σ u = {!   !}

Ω : U
Ω = {!   !}

