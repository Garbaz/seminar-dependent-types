open import Agda.Primitive using (Setω)

P : Setω → Setω
P S = S → Setω

U : Setω
U = ∀ (X : Setω) → (P (P X) → X) → P (P X)

τ : P (P U) → U
τ t X f p = t (λ x → p (f (x X f)))

σ : U → P (P U)
σ s = s U τ

pu : {A : Set} → P U
pu {A} y = (∀ p → σ y p → p (τ (σ y))) → A

ppu : P (P U)
ppu p = (∀ x → σ x p → p x)

u : U
u = τ ppu

R : ∀ p → ppu p → p u
R _ 𝟙 = 𝟙 u (λ x → 𝟙 (τ (σ x)))

M : {A : Set} → ∀ x → σ x (pu {A}) → pu x
M _ 𝟚 𝟛 = 𝟛 pu 𝟚 (λ p → 𝟛 (λ y → p (τ (σ y))))

L : {A : Set} → (∀ p → ppu p → p u) → A
L 𝟘 = 𝟘 pu M (λ p → 𝟘 (λ y → p (τ (σ y))))

evil : {A : Set} → A
evil = L R

data ⊥ : Set where

false : ⊥
false = evil
