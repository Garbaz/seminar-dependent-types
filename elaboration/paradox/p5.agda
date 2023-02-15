{-# OPTIONS --type-in-type #-}

⊥ : Set
⊥ = {A : Set} → A

¬ : Set → Set
¬ P = P → ⊥

℘ : Set → Set
℘ A = A → Set

U : Set
U = (A : Set) → (℘ (℘ A) → A) → ℘ (℘ A)

τ : ℘ (℘ U) → U
τ ppU A ppA→A pA = ppU (λ u → pA (ppA→A (u A ppA→A)))

σ : U → ℘ (℘ U)
σ u = u U τ

-- Δ : ℘ U
-- Δ u = ¬ ((pU : ℘ U) → σ u pU → pU (τ (σ u)))

_<_ : U → U → Set
v < u = (pU : ℘ U) → σ u pU → pU v

lemma1 : {u v : U} → v < u → τ (σ v) < τ (σ u)
lemma1 v<u pU q = {!   !}

inductive' : ℘ (℘ U)
inductive' pU = (u : U) → σ u pU → pU u

Ω : U
Ω = τ inductive'

well-founded : ℘ U
well-founded u = (pU : ℘ U) → inductive' pU → pU u


lemma2 : (pU : ℘ U) → inductive' pU → inductive' (λ u → pU (τ (σ u)) → Set)
lemma2 pU ind-pU u q pUτσu = {!   !}

wfΩ : well-founded Ω
wfΩ pU ind-pU = ind-pU Ω (λ u → {!   !})

¬wfΩ : ¬ (well-founded Ω)
¬wfΩ wfΩ = {!   !}