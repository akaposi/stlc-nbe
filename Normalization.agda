
module Normalization where

open import Lib
open import UIP
open import Syntax
open import Renaming
open import Substitution
open import Nf

infixl 8 _ᴺ[_]ᵣ

Tmᴺ : Con → Ty → Set
Tmᴺ Γ ι       = Nf Γ ι
Tmᴺ Γ (A ⇒ B) = ∀ {Δ} → Ren Δ Γ → Tmᴺ Δ A → Tmᴺ Δ B

data Tmsᴺ (Γ : Con) : Con → Set where
  ∙   : Tmsᴺ Γ ∙
  _,_ : ∀ {A Δ} (σ : Tmsᴺ Γ Δ)(t : Tmᴺ Γ A) → Tmsᴺ Γ (Δ , A)
infixr 5 _,_

_ᴺ[_]ᵣ : ∀ {A Γ Δ} → Tmᴺ Γ A → Ren Δ Γ → Tmᴺ Δ A
_ᴺ[_]ᵣ {ι}     = _[_]ₙᵣ
_ᴺ[_]ᵣ {A ⇒ B} = λ fᴺ σ δ → fᴺ (σ ∘ᵣ δ)

_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ} → Tmsᴺ Δ Σ → Ren Γ Δ → Tmsᴺ Γ Σ
∙       ᴺ∘ᵣ δ = ∙
(σ , t) ᴺ∘ᵣ δ = (σ ᴺ∘ᵣ δ) , (t ᴺ[ δ ]ᵣ)

∈↑ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Tmsᴺ Δ Γ → Tmᴺ Δ A
∈↑ᴺ vz     (σ , t) = t
∈↑ᴺ (vs v) (σ , t) = ∈↑ᴺ v σ

Tm↑ᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Tmsᴺ Δ Γ → Tmᴺ Δ A
Tm↑ᴺ (var v)   σ = ∈↑ᴺ v σ
Tm↑ᴺ (lam t)   σ = λ δ aᴺ → Tm↑ᴺ t (σ ᴺ∘ᵣ δ , aᴺ)
Tm↑ᴺ (app f a) σ = Tm↑ᴺ f σ idᵣ (Tm↑ᴺ a σ)

mutual
  qᴺ : ∀ {Γ A} → Tmᴺ Γ A → Nf Γ A
  qᴺ {A = ι}     tᴺ = tᴺ
  qᴺ {A = A ⇒ B} tᴺ = lam (qᴺ (tᴺ wk (uᴺ (var vz))))

  uᴺ : ∀ {Γ A} → Ne Γ A → Tmᴺ Γ A
  uᴺ {A = ι}     n = ne n
  uᴺ {A = A ⇒ B} n = λ δ aᴺ → uᴺ (app (n [ δ ]ₙₑᵣ) (qᴺ aᴺ))

idᴺₛ : ∀ {Γ} → Tmsᴺ Γ Γ
idᴺₛ {∙}     = ∙
idᴺₛ {Γ , t} = idᴺₛ {Γ} ᴺ∘ᵣ wk , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tm↑ᴺ t idᴺₛ)

