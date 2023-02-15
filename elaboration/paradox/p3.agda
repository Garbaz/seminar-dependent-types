{-# OPTIONS --type-in-type #-}

⊥ : Set
⊥ = (A : Set) → A

¬ : Set → Set
¬ A = A → ⊥

-- "Propositions over A", or the "Powerset of A, aka. 2ᴬ"
℘ : Set → Set
℘ A = A → Set

-- Our paradoxical universe
U : Set
U = (A : Set) → ((℘ A) → A) → ℘ A

τ : ℘ U → U
τ pu A pa→a a = (pa : ℘ A) → ((u : U) → pu u → pa (pa→a (u A pa→a))) → pa a

σ : U → ℘ U
σ u = u U τ

paradoxU∈ : (X : ℘ U) → (u : U) → X u → (σ (τ X)) (τ (σ u))
paradoxU∈ X u Xu pU f = {!   !}

_<_ : U → U → Set
u < v = σ v u

lemma1 : {u v : U} → u < v → τ (σ u) < τ (σ v)
lemma1 {u} {_} u<v _ f = f u u<v

inductive' : ℘ (℘ U)
inductive' pu = (v : U) → ((u : U) → u < v → pu u) → pu v

well-founded : ℘ U
well-founded u = (pu : ℘ U) → inductive' pu → pu u

-- qqq : (u : U) → well-founded (τ (σ u)) → well-founded u
-- qqq u wf-τσu pu ind-pu = ind-pu u λ v v<u → {!   !}

Ω : U
Ω = τ well-founded

-- 𝓛₂ : (w : U) → τ (σ w) < Ω → well-founded w
-- 𝓛₂ w τσw<Ω pu ind-pu = ind-pu (τ (σ w)) (λ u u<w → ind-pu {!   !} {!   !})

-- pred : U → ℘ U
-- pred = σ

-- qq : (w : U) → (σ Ω) (τ (σ w)) → well-founded w
-- qq w pΩτσw = λ pu ind-pu → ind-pu w λ u u<w → {!   !}

-- q : (X : ℘ U) → inductive' X → X Ω
-- -- q X ind-X = ind-X Ω λ u u<Ω → u<Ω X λ v wf-v → {! wf-v X ind-X  !}
-- q X ind-X = ind-X Ω λ u u<Ω → u<Ω {! λ u → X (τ (σ u))  !} {!   !}

-- q'' : (X : ℘ U) → inductive' X → inductive' (λ u → X (τ (σ u)))
-- q'' X ind-X u uu = ind-X (τ (σ u)) λ v v<τσu → {!   !}

-- q' : (X : ℘ U) → (u : U) → X (τ (σ u)) → X u
-- q' X u Xτσu = {!   !}

wfΩ : well-founded Ω
-- wfΩ pu ind-pu = ind-pu Ω (λ u u<Ω → {!   !})
wfΩ pu ind-pu = ind-pu Ω λ u u<Ω → {!   !}

¬wfΩ : ¬ (well-founded Ω)
¬wfΩ p = {! p (τ (σ Ω))  !}



U' : Set
U' = (A : Set) → (A → A → Set) → A → Set

σ' : U' → ℘ U'
σ' u v = {!   !}