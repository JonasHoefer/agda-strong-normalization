{-# OPTIONS --safe --without-K #-}

open import Term
open import Term.Neutral.Base
open import Term.StrongNormalization
open import Renaming
open import Substitution
open import Reduction

module Term.Neutral.Properties where

NE-closed-▷ : {t u : Γ ⊢ τ} → t ▷ u → NE t → NE u
NE-closed-▷ (ξ₁ s▷s′) (s∈NE ∙ t∈SN) = NE-closed-▷ s▷s′ s∈NE ∙ t∈SN
NE-closed-▷ (ξ₂ t▷t′) (s∈NE ∙ sn p) = s∈NE ∙ p _ t▷t′

-- we package the termination for pairs in a single type such that Agda recognises that a single argument 
-- decreases in NE⊆SN-∙. 
data SN-× (t : Γ ⊢ τ₁) (s : Γ ⊢ τ₂) : Set where
  sn-× : (∀ t′ → t ▷ t′ → SN-× t′ s) → (∀ s′ → s ▷ s′ → SN-× t s′) → SN-× t s

sn-×-acc : (t : Γ ⊢ τ₁) (s : Γ ⊢ τ₂) → SN t → SN s → SN-× t s
sn-×-acc t s p@(sn t∈SN) q@(sn s∈SN) = sn-× (λ t′ t▷t′ → sn-×-acc t′ s (t∈SN t′ t▷t′) q) (λ s′ s▷s′ → sn-×-acc t s′ p (s∈SN s′ s▷s′))

NE⊆SN-∙ : (t : Γ ⊢ (τ₁ ⇒ τ₂)) (s : Γ ⊢ τ₁) → NE t → SN-× t s → SN (t ∙ s)
NE⊆SN-∙ t s t∈NE (sn-× p q) = sn λ where -- note that t∈NE limits the cases for ↝
  (u ∙ s) (ξ₁ t▷u) → NE⊆SN-∙ u s (NE-closed-▷ t▷u t∈NE) (p u t▷u)
  (t ∙ u) (ξ₂ u▷s) → NE⊆SN-∙ t u t∈NE                   (q u u▷s)

NE⊆SN : (t : Γ ⊢ τ) → NE t → SN t
NE⊆SN (var x) (var x)       = sn λ where u ()
NE⊆SN (t ∙ s) (t∈NE ∙ s∈SN) = NE⊆SN-∙ t s t∈NE (sn-×-acc t s (NE⊆SN t t∈NE) s∈SN)

renaming-NE : (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → NE t → NE (ρ ⟪ t ⟫)
renaming-NE ρ (var x) (var x)       = var (ρ ⟨ x ⟩)
renaming-NE ρ (t ∙ u) (t∈NE ∙ u∈SN) = renaming-NE ρ t t∈NE ∙ renaming-SN ρ u u∈SN
