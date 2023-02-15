open import Level renaming (suc to lsuc)

-- Propositions over type A
P : ∀ {ℓ} → Set ℓ → Set (lsuc ℓ)
P {ℓ} A = A → Set ℓ

-- Propositions over propositions over type A
PP : ∀ {ℓ} → Set ℓ → Set (lsuc (lsuc ℓ))
PP A = P (P A)

Pω : Setω → Setω₁
Pω A = A → Setω

PPω : Setω → Setω₁
PPω A = (A → Setω) → Setω

U : Set₂
U = (A : Set) → (PP A → A) → PP A

τ : PP U → U
τ ppu A ppa→a pa = {!  !} -- ppu λ u → pa (ppa→a (u A ppa→a))

σ : U → PP U
σ u = {!   !} -- u U τ

PU₀ : {A : Set} → P U
PU₀ {A} u = {!   !} -- (pu : P U) → σ u pu → pu (τ (σ u)) → A

PPU₀ : PP U
PPU₀ pu = (u : U) → σ u pu → pu u

U₀ : U
U₀ = τ PPU₀

R : (pu : P U) → PPU₀ pu → pu U₀
R _ ppu₀pu = ppu₀pu U₀ λ u → ppu₀pu (τ (σ u))

M : {A : Set} → (u : U) → σ u (PU₀ {A}) → PU₀ {A} u
M {A} u σupu₀ pu = {!   !}