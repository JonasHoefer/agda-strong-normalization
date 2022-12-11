{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Term
open import Renaming
open import Substitution

module Reduction.Base where

infix 5 _▷_ -- _↜_
infix 5 _▶⋆_
data _▷_ : Γ ⊢ τ → Γ ⊢ τ → Set where
  ξ₁ :  {t : Γ ⊢ τ₁} {s s' : Γ ⊢ τ₁ ⇒ τ}
     → s ▷ s'
     → s ∙ t ▷ s' ∙ t

  ξ₂ : {s : Γ ⊢ τ₁ ⇒ τ} {t t' : Γ ⊢ τ₁}
     → t ▷ t'
     → s ∙ t ▷ s ∙ t'

  β : {s : Γ , τ₁ ⊢ τ} {t : Γ ⊢ τ₁}
    → abs s ∙ t ▷ s [ t ]

  ζ : {s t : Γ , τ₁ ⊢ τ}
    → s ▷ t
    → abs s ▷ abs t

infixr 5 _▷⁺_
infixr 2 _▷⁺step_
data _▷⁺_ : Γ ⊢ τ → Γ ⊢ τ → Set where
  _▷⁺end : {s t : Γ ⊢ τ} → s ▷ t → s ▷⁺ t
  _▷⁺step_ : {s t r : Γ ⊢ τ} → s ▷ t → t ▷⁺ r → s ▷⁺ r

-- Often, we want to explicitly use ▷⁺ because this relation is SN.
-- Furthermore, having an explicit proof for the equality is more convinient than a constructor in the reflexive transitive closure.
infix 5 _▷⋆_
_▷⋆_ : Γ ⊢ τ → Γ ⊢ τ → Set 
_▷⋆_ s t = s ≡ t ⊎ s ▷⁺ t

_▶⋆_ : Subst Γ Δ → Subst Γ Δ → Set
σ₁ ▶⋆ σ₂ = {τ : Type} (x : _ ∋ τ) → (σ₁ ⟨ x ⟩ˢ) ▷⋆ (σ₂ ⟨ x ⟩ˢ)
