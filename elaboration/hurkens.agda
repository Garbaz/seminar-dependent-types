{-# OPTIONS --type-in-type #-}

-- An implementation of one of Hurkens' simplifications of Girard's Paradox.
-- Adapted from "A Simplification of Girard's Paradox", Hurkens 1995.
-- "✨" marks definitions which are pulled out of thin air.
-- "_term_" marks terms which are defined there and then.

-- | The empty type.
⊥ : Set
⊥ = {A : Set} → A

-- | Negation of a predicate.
¬ : Set → Set
¬ P = P → ⊥

-- | The set of all predicates over A; Or the set of all subsets of A.
℘ : Set → Set
℘ A = A → Set

-- | ✨ A _powerful_ universe.
U : Set
U = (A : Set) → (℘ (℘ A) → A) → ℘ (℘ A)

-- | ✨ The τ for our powerful universe.
τ : ℘ (℘ U) → U
τ ppU A ppA→A pA = ppU (λ u → pA (ppA→A (u A ppA→A)))

-- | ✨ The σ for our powerful universe.
σ : U → ℘ (℘ U)
σ u = u U τ

-- | A pU is _inductive_ iff for every u, if pU is in (σ u), then u is in pU.
inductive' : ℘ (℘ U)
inductive' pU = ((u : U) → σ u pU → pU u)

-- | ✨ We pick a specific element from U for which we will find our contradiction.
Ω : U
Ω = τ inductive'

-- | A u is _well-founded_ iff it is in every inductive pU.
well-founded : ℘ U
well-founded u = (pU : ℘ U) → inductive' pU → pU u

-- | We prove that Ω is well-founded.
well-founded-Ω : well-founded Ω
well-founded-Ω pU ind-pU = ind-pU Ω (λ u → ind-pU (τ (σ u)))

-- | A v is a _predecessor_ of a u iff for every pU in (σ u), v is in pU.
_<_ : U → U → Set
v < u = (pU : ℘ U) → σ u pU → pU v

-- | ✨ The set of all u such that τ (σ u) ≮ u.
Δ : ℘ U
Δ u = ¬ (τ (σ u) < u)

-- | We prove that Δ is inductive.
ind-Δ : inductive' Δ
ind-Δ u σuΔ τσu<u = τσu<u Δ σuΔ (λ pU → τσu<u λ w → pU (τ (σ w)))

-- | We prove that Ω is not well-founded.
¬well-founded-Ω : ¬ (well-founded Ω)
¬well-founded-Ω wfΩ = wfΩ Δ ind-Δ (λ pU → wfΩ (λ v → pU (τ (σ v))))

-- | 😨 And from this contradiction, we get a term of type ⊥.
false : ⊥
false = ¬well-founded-Ω well-founded-Ω
