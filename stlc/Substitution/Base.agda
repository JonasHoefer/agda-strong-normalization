{-# OPTIONS --safe --without-K #-}

open import Term
open import Renaming

module Substitution.Base where

infixl 10 _◆_
infixl 10 _⬖_
infixl 10 _⬗_
infixl 9 _⟨_⟩ˢ
infixl 9 _⟪_⟫ˢ
infixl 8 _[_]

data Subst : Ctx → Ctx → Set where
  ∅   : Subst ∅ Δ
  _∷_ : Δ ⊢ τ → Subst Γ Δ → Subst (Γ , τ) Δ

suc-subst : Subst Γ Δ → Subst Γ (Δ , τ)
suc-subst ∅       = ∅
suc-subst (t ∷ σ) = suc-renaming (idᴿ _) ⟪ t ⟫ ∷ suc-subst σ

exts : Subst Γ Δ → Subst (Γ , τ) (Δ , τ)
exts σ = var Z ∷ suc-subst σ

_⟨_⟩ˢ : Subst Γ Δ → Γ ∋ τ → Δ ⊢ τ
(t ∷ _) ⟨ Z ⟩ˢ = t 
(_ ∷ σ) ⟨ S x ⟩ˢ = σ ⟨ x ⟩ˢ

_⟪_⟫ˢ : Subst Γ Δ → Γ ⊢ τ → Δ ⊢ τ
σ ⟪ var x ⟫ˢ = σ ⟨ x ⟩ˢ
σ ⟪ s ∙ t ⟫ˢ = σ ⟪ s ⟫ˢ ∙ σ ⟪ t ⟫ˢ
σ ⟪ abs t ⟫ˢ = abs (exts σ ⟪ t ⟫ˢ)

_◆_ : Subst Δ Ω → Subst Γ Δ → Subst Γ Ω
σ₂ ◆ ∅ = ∅
σ₂ ◆ (t ∷ σ₁) = σ₂ ⟪ t ⟫ˢ ∷ σ₂ ◆ σ₁

idˢ : (Γ : Ctx) → Subst Γ Γ
idˢ ∅ = ∅
idˢ (Γ , x) = exts (idˢ Γ)

_⬖_ : Renaming Δ Ω → Subst Γ Δ → Subst Γ Ω
ρ ⬖ ∅ = ∅
ρ ⬖ (t ∷ σ) = ρ ⟪ t ⟫ ∷ ρ ⬖ σ

_⬗_ : Subst Δ Ω → Renaming Γ Δ → Subst Γ Ω
σ ⬗ ∅ = ∅
σ ⬗ (x ∷ ρ) = σ ⟨ x ⟩ˢ ∷ σ ⬗ ρ

substOuter : (s : Γ ⊢ τ) → Subst (Γ , τ) Γ
substOuter s = (s ∷ idˢ _) 

_[_] : Γ , τ₁ ⊢ τ₂ → Γ ⊢ τ₁ → Γ ⊢ τ₂
t [ s ] = substOuter s ⟪ t ⟫ˢ

lift : Renaming Γ Δ → Subst Γ Δ
lift ∅       = ∅
lift (x ∷ ρ) = var x ∷ lift ρ
