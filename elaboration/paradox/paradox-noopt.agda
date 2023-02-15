-- {-# OPTIONS --type-in-type #-}

open import Level renaming (suc to lsuc)

data ⊥ : Set where

pow : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
pow {ℓ} S = S → Set ℓ

U : ∀ {ℓ} → Set (lsuc (lsuc ℓ))
U {ℓ} = ∀ (X : Set ℓ) → (pow (pow X) → X) → pow (pow X)

τ : pow (pow U) → U
τ t X f p = t λ x → p (f (x X f))

σ : U → pow (pow U)
σ s = s U τ

pU : pow U
pU y = (∀ p → σ y p → p (τ (σ y))) → ⊥

ppU : (pow (pow U))
ppU p = (∀ x → σ x p → p x)

Ω : U
Ω = τ ppU

R : ∀ p → ppU p → p Ω
R _ 𝟙 = 𝟙 Ω λ x → 𝟙 (τ (σ x))

M : ∀ x → σ x pU → pU x
M _ 𝟚 𝟛 = 𝟛 pU 𝟚 (λ p → 𝟛 λ y → p (τ (σ y)))

L : (∀ p → ppU p → p Ω) → ⊥
L 𝟘 = 𝟘 pU M (λ p → 𝟘 (λ y → p (τ (σ y))))

false : ⊥
false = L R 