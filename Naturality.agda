
module Naturality where

open import Lib
open import Syntax
open import Renaming
open import Substitution
open import Normalization
open import Nf

Tmᴺⁿ : ∀ {Γ A} → Tmᴺ Γ A → Set
Tmᴺⁿ {Γ}{A = ι} tᴺ = ⊤
Tmᴺⁿ {Γ}{A ⇒ B} tᴺ =
  ∀ {Δ Σ}(σ : Ren Δ Γ)(δ : Ren Σ Δ){aᴺ}
  → Tmᴺⁿ aᴺ → (tᴺ σ aᴺ ᴺ[ δ ]ᵣ ≡ tᴺ (σ ∘ᵣ δ) (aᴺ ᴺ[ δ ]ᵣ)) × Tmᴺⁿ (tᴺ σ aᴺ ᴺ[ δ ]ᵣ)

data Tmsᴺⁿ {Γ : Con} : ∀ {Δ} → Tmsᴺ Γ Δ → Set where
  ∙   : Tmsᴺⁿ ∙
  _,_ : ∀ {A Δ}{σ : Tmsᴺ Γ Δ}{tᴺ : Tmᴺ Γ A} → Tmsᴺⁿ σ → Tmᴺⁿ tᴺ → Tmsᴺⁿ (σ , tᴺ)

ᴺ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tmᴺ Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t ᴺ[ σ ]ᵣ ᴺ[ δ ]ᵣ ≡ t ᴺ[ σ ∘ᵣ δ ]ᵣ
ᴺ∘ᵣTm {A = ι}     t σ δ = ∘ᵣNf t σ δ
ᴺ∘ᵣTm {A = A ⇒ B} t σ δ = exti λ _ → ext λ ν → t & (assᵣ σ δ ν ⁻¹)

infixl 8 _ᴺⁿ[_]ᵣ
_ᴺⁿ[_]ᵣ : ∀ {Γ Δ A}{tᴺ : Tmᴺ Γ A} → Tmᴺⁿ tᴺ → (σ : Ren Δ Γ) → Tmᴺⁿ (tᴺ ᴺ[ σ ]ᵣ)
_ᴺⁿ[_]ᵣ {A = ι}     tᴺⁿ σ = tt
_ᴺⁿ[_]ᵣ {A = A ⇒ B} tᴺⁿ σ δ ν aᴺⁿ rewrite assᵣ σ δ ν ⁻¹ = tᴺⁿ (σ ∘ᵣ δ) ν aᴺⁿ

infixr 6 _ᴺⁿ∘ᵣ_
_ᴺⁿ∘ᵣ_ : ∀ {Γ Δ Σ}{σᴺ : Tmsᴺ Δ Σ} → Tmsᴺⁿ σᴺ → (δ : Ren Γ Δ) →  Tmsᴺⁿ (σᴺ ᴺ∘ᵣ δ)
∙           ᴺⁿ∘ᵣ δ = ∙
(σᴺⁿ , tᴺⁿ) ᴺⁿ∘ᵣ δ = (σᴺⁿ ᴺⁿ∘ᵣ δ) , tᴺⁿ ᴺⁿ[ δ ]ᵣ

assᴺᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tmsᴺ Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ᴺ∘ᵣ δ) ᴺ∘ᵣ ν ≡ σ ᴺ∘ᵣ (δ ∘ᵣ ν)
assᴺᵣᵣ ∙       δ ν = refl
assᴺᵣᵣ (σ , t) δ ν = _,_ & assᴺᵣᵣ σ δ ν ⊗ ᴺ∘ᵣTm t δ ν

idᵣTmᴺ : ∀ {Γ A}(t : Tmᴺ Γ A) → t ᴺ[ idᵣ ]ᵣ ≡ t
idᵣTmᴺ {A = ι}     t = idᵣNf t
idᵣTmᴺ {A = A ⇒ B} t = exti λ _ → ext λ σ → t & idlᵣ σ

∈↑ᴺⁿ : ∀ {Γ A} → (v : A ∈ Γ) → ∀ {Δ σ} → Tmsᴺⁿ {Δ}{Γ} σ → Tmᴺⁿ (∈↑ᴺ v σ)
∈↑ᴺⁿ vz     (σⁿ , tⁿ) = tⁿ
∈↑ᴺⁿ (vs v) (σⁿ , _ ) = ∈↑ᴺⁿ v σⁿ

∈↑ᴺ-nat :
  ∀ {Γ Δ A}(v : A ∈ Γ){σᴺ} → Tmsᴺⁿ σᴺ
  → ∀ {Σ}(δ : Ren Σ Δ) → ∈↑ᴺ v (σᴺ ᴺ∘ᵣ δ) ≡ ∈↑ᴺ v σᴺ ᴺ[ δ ]ᵣ
∈↑ᴺ-nat vz     (σᴺⁿ , _) δ = refl
∈↑ᴺ-nat (vs v) (σᴺⁿ , x) δ = ∈↑ᴺ-nat v σᴺⁿ δ

uᴺ-nat : ∀ {A Γ Δ} → (n : Ne Γ A) → (σ : Ren Δ Γ) → uᴺ n ᴺ[ σ ]ᵣ ≡ uᴺ (n [ σ ]ₙₑᵣ)
uᴺ-nat {ι}     n σ = refl
uᴺ-nat {A ⇒ B} n σ = exti λ _ → ext λ δ → ext λ aᴺ → (λ x → uᴺ (app x (qᴺ aᴺ))) & (∘ᵣNe n σ δ ⁻¹)

mutual
  Tm↑ᴺ-nat : 
    ∀ {Γ Δ A}(t : Tm Γ A) {σᴺ} → Tmsᴺⁿ σᴺ
    → ∀ {Σ}(δ : Ren Σ Δ) → Tm↑ᴺ t (σᴺ ᴺ∘ᵣ δ) ≡ Tm↑ᴺ t σᴺ ᴺ[ δ ]ᵣ
  Tm↑ᴺ-nat (var v)   σᴺⁿ δ = ∈↑ᴺ-nat v σᴺⁿ δ
  Tm↑ᴺ-nat (lam t)   σᴺⁿ δ =
    exti λ _ → ext λ ν → ext λ aᴺ → (λ x → Tm↑ᴺ t (x , aᴺ)) & (assᴺᵣᵣ _ _ _)
  Tm↑ᴺ-nat (app f a) {σᴺ} σᴺⁿ δ
    rewrite Tm↑ᴺ-nat f σᴺⁿ δ | Tm↑ᴺ-nat a σᴺⁿ δ =
        (λ x → Tm↑ᴺ f σᴺ x (Tm↑ᴺ a σᴺ ᴺ[ δ ]ᵣ)) & (idrᵣ δ ◾ idlᵣ δ ⁻¹)
      ◾ proj₁ (Tm↑ᴺⁿ f σᴺⁿ idᵣ δ (Tm↑ᴺⁿ a σᴺⁿ)) ⁻¹ 

  Tm↑ᴺⁿ : ∀ {Γ A} → (t : Tm Γ A) → ∀ {Δ σᴺ} → Tmsᴺⁿ {Δ}{Γ} σᴺ → Tmᴺⁿ (Tm↑ᴺ t σᴺ)
  Tm↑ᴺⁿ (var v)   σᴺⁿ = ∈↑ᴺⁿ v σᴺⁿ
  Tm↑ᴺⁿ (lam t) {σ}{σᴺ} σᴺⁿ = λ δ ν {aᴺ} aᴺⁿ →
     (Tm↑ᴺ-nat t (σᴺⁿ ᴺⁿ∘ᵣ δ , aᴺⁿ) ν ⁻¹ ◾ (λ x → Tm↑ᴺ t (x , aᴺ ᴺ[ ν ]ᵣ)) & assᴺᵣᵣ σᴺ δ ν)
     , Tm↑ᴺⁿ t (σᴺⁿ ᴺⁿ∘ᵣ δ , aᴺⁿ) ᴺⁿ[ ν ]ᵣ
  Tm↑ᴺⁿ (app f a) σᴺⁿ = coe (Tmᴺⁿ & idᵣTmᴺ _) (proj₂ (Tm↑ᴺⁿ f σᴺⁿ idᵣ idᵣ (Tm↑ᴺⁿ a σᴺⁿ)))

mutual
  qᴺ-nat : ∀ {A Γ Δ}(tᴺ : Tmᴺ Γ A)(σ : Ren Δ Γ) → Tmᴺⁿ tᴺ → qᴺ tᴺ [ σ ]ₙᵣ ≡ qᴺ (tᴺ ᴺ[ σ ]ᵣ)
  qᴺ-nat {ι}     tᴺ σ tᴺⁿ = refl
  qᴺ-nat {A ⇒ B} tᴺ σ tᴺⁿ = lam &
      (qᴺ-nat (tᴺ wk (uᴺ (var vz))) (keep σ)
        (let (p , q) = tᴺⁿ wk idᵣ (uᴺⁿ (var vz)) in 
          coe (Tmᴺⁿ & (p ◾ tᴺ & (drop & idrᵣ idᵣ) ⊗ uᴺ-nat (var vz) (keep idᵣ))) q)
    ◾ qᴺ & (proj₁ (tᴺⁿ wk (keep σ) (uᴺⁿ (var vz)))
    ◾ tᴺ & (drop & (idlᵣ σ ◾ idrᵣ σ ⁻¹)) ⊗ uᴺ-nat (var vz) (keep σ)))

  uᴺⁿ : ∀ {Γ A}(n : Ne Γ A) → Tmᴺⁿ (uᴺ n)
  uᴺⁿ {A = ι}     n = tt
  uᴺⁿ {A = A ⇒ B} n σ δ {aᴺ} aᴺⁿ =
      (uᴺ-nat (app (n [ σ ]ₙₑᵣ) (qᴺ aᴺ)) δ
    ◾ (λ x → uᴺ (app (n [ σ ]ₙₑᵣ [ δ ]ₙₑᵣ) x)) & qᴺ-nat aᴺ δ aᴺⁿ
    ◾ (λ f → f δ (aᴺ ᴺ[ δ ]ᵣ)) & uᴺ-nat n σ ⁻¹) ,    
    uᴺⁿ (app (n [ σ ]ₙₑᵣ) (qᴺ aᴺ)) ᴺⁿ[ δ ]ᵣ

idᴺⁿₛ : ∀ {Γ} → Tmsᴺⁿ (idᴺₛ {Γ})
idᴺⁿₛ {∙}     = ∙
idᴺⁿₛ {Γ , A} = (idᴺⁿₛ ᴺⁿ∘ᵣ wk) , uᴺⁿ (var vz)

--------------------------------------------------------------------------------

infixr 6 _ₛ∘ᴺ_
_ₛ∘ᴺ_ : ∀ {Γ Δ Σ} → Tms Γ Δ → Tmsᴺ Σ Γ → Tmsᴺ Σ Δ
∙       ₛ∘ᴺ δ = ∙
(σ , t) ₛ∘ᴺ δ = (σ ₛ∘ᴺ δ) , Tm↑ᴺ t δ

idrᴺᵣ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → σ ᴺ∘ᵣ idᵣ ≡ σ
idrᴺᵣ ∙       = refl
idrᴺᵣ (σ , t) = _,_ & idrᴺᵣ σ ⊗ idᵣTmᴺ t

infixr 6 _ᵣ∘ᴺ_
_ᵣ∘ᴺ_ : ∀ {Γ Δ Σ} → Ren Γ Δ → Tmsᴺ Σ Γ → Tmsᴺ Σ Δ
∙      ᵣ∘ᴺ δ       = δ
drop σ ᵣ∘ᴺ (δ , t) = σ ᵣ∘ᴺ δ
keep σ ᵣ∘ᴺ (δ , t) = (σ ᵣ∘ᴺ δ) , t

∈↑ᴺ-nat₁ :
  ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : Ren Δ Γ)(δ : Tmsᴺ Σ Δ)
  → ∈↑ᴺ (v [ σ ]∈ᵣ) δ ≡ ∈↑ᴺ v (σ ᵣ∘ᴺ δ)
∈↑ᴺ-nat₁ ()     ∙        δ
∈↑ᴺ-nat₁ v      (drop σ) (δ , t) = ∈↑ᴺ-nat₁ v σ δ
∈↑ᴺ-nat₁ vz     (keep σ) (δ , t) = refl
∈↑ᴺ-nat₁ (vs v) (keep σ) (δ , t) = ∈↑ᴺ-nat₁ v σ δ

assᵣᴺᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Tmsᴺ Δ Σ)(ν : Ren Γ Δ)
  → (σ ᵣ∘ᴺ δ) ᴺ∘ᵣ ν ≡ σ ᵣ∘ᴺ δ ᴺ∘ᵣ ν
assᵣᴺᵣ ∙        δ       ν = refl
assᵣᴺᵣ (drop σ) (δ , t) ν = assᵣᴺᵣ σ δ ν
assᵣᴺᵣ (keep σ) (δ , t) ν = (_, t ᴺ[ ν ]ᵣ) & assᵣᴺᵣ σ δ ν

Tm↑ᴺ-nat₁ :
  ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : Ren Δ Γ)(δ : Tmsᴺ Σ Δ)
  → Tm↑ᴺ (t [ σ ]ᵣ) δ ≡ Tm↑ᴺ t (σ ᵣ∘ᴺ δ)
Tm↑ᴺ-nat₁ (var v)   σ δ = ∈↑ᴺ-nat₁ v σ δ
Tm↑ᴺ-nat₁ (lam t)   σ δ = exti λ _ → ext λ ν → ext λ aᴺ →
    Tm↑ᴺ-nat₁ t (keep σ) (δ ᴺ∘ᵣ ν , aᴺ)
  ◾ (λ x → Tm↑ᴺ t (x , aᴺ)) & (assᵣᴺᵣ σ δ ν ⁻¹)
Tm↑ᴺ-nat₁ (app f a) σ δ
  rewrite Tm↑ᴺ-nat₁ f σ δ | Tm↑ᴺ-nat₁ a σ δ = refl

idlᴺᵣ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → idᵣ ᵣ∘ᴺ σ ≡ σ
idlᴺᵣ ∙       = refl
idlᴺᵣ (σ , t) = (_, t) & idlᴺᵣ σ

assₛᵣᴺ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Tmsᴺ Γ Δ)
  → (σ ₛ∘ᵣ δ) ₛ∘ᴺ ν ≡ σ ₛ∘ᴺ δ ᵣ∘ᴺ ν
assₛᵣᴺ ∙       δ ν = refl
assₛᵣᴺ (σ , t) δ ν = _,_ & assₛᵣᴺ σ δ ν ⊗ Tm↑ᴺ-nat₁ t δ ν

assₛᴺᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ){δ : Tmsᴺ Δ Σ}(_ : Tmsᴺⁿ δ)(ν : Ren Γ Δ)
  → (σ ₛ∘ᴺ δ) ᴺ∘ᵣ ν ≡ σ ₛ∘ᴺ δ ᴺ∘ᵣ ν
assₛᴺᵣ ∙       δⁿ ν = refl
assₛᴺᵣ (σ , t) δⁿ ν = _,_ & assₛᴺᵣ σ δⁿ ν ⊗ (Tm↑ᴺ-nat t δⁿ ν ⁻¹)

idlᴺₛ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → σ ≡ idₛ ₛ∘ᴺ σ
idlᴺₛ ∙       = refl
idlᴺₛ (σ , t) =
  (_, t) & (((idlᴺᵣ σ ⁻¹ ◾ idlᴺₛ (idᵣ ᵣ∘ᴺ σ)) ◾ assₛᵣᴺ idₛ wk (σ , t) ⁻¹))

ₛ∘ᴺ∈↑ :
  ∀ {Γ Δ Σ A}(v : A ∈ Δ)(σ : Tms Γ Δ)(δ : Tmsᴺ Σ Γ)
  → Tm↑ᴺ (v [ σ ]∈) δ ≡ ∈↑ᴺ v (σ ₛ∘ᴺ δ)
ₛ∘ᴺ∈↑ vz     (σ , t) δ = refl
ₛ∘ᴺ∈↑ (vs v) (σ , t) δ = ₛ∘ᴺ∈↑ v σ δ

ₛ∘ᴺ↑ :
  ∀ {Γ Δ Σ A}(t : Tm Δ A)(σ : Tms Γ Δ){δ : Tmsᴺ Σ Γ}(δᴺ : Tmsᴺⁿ δ)
  → Tm↑ᴺ (t [ σ ]) δ ≡ Tm↑ᴺ t (σ ₛ∘ᴺ δ)
ₛ∘ᴺ↑ (var v)   σ {δ} δⁿ = ₛ∘ᴺ∈↑ v σ δ
ₛ∘ᴺ↑ (lam t)   σ {δ} δⁿ = exti λ Δ → ext λ ν →
  ext λ aᴺ → {!!}


-- exti λ _ → ext λ ν → ext λ aᴺ →
--     ₛ∘ᴺ↑ t (keepₛ σ) (δⁿ ᴺⁿ∘ᵣ ν , aᴺ)
--   ◾ (λ x → Tm↑ᴺ t ((x , aᴺ))) &
--       (assₛᵣᴺ σ wk (δ ᴺ∘ᵣ ν , aᴺ)
--     ◾ (σ ₛ∘ᴺ_) & idlᴺᵣ (δ ᴺ∘ᵣ ν)
--     ◾ assₛᴺᵣ σ δ ν ⁻¹)
ₛ∘ᴺ↑ (app f a) σ δ
  rewrite ₛ∘ᴺ↑ f σ δ | ₛ∘ᴺ↑ a σ δ = refl

