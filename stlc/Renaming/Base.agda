{-# OPTIONS --safe --without-K #-}

open import Term

module Renaming.Base where

infixr 5 _∷_
infixl 10 _◇_
infixl 9 _⟨_⟩
infixl 9 _⟪_⟫

data Renaming : Ctx → Ctx → Set where
  ∅   : Renaming ∅ Δ
  _∷_ : Δ ∋ τ → Renaming Γ Δ → Renaming (Γ , τ) Δ

private variable ρ ρ₁ ρ₂ : Renaming Γ Δ

suc-renaming : Renaming Γ Δ → Renaming Γ (Δ , τ)
suc-renaming ∅ = ∅
suc-renaming (x ∷ ρ) = S x ∷ suc-renaming ρ

ext : Renaming Γ Δ → Renaming (Γ , τ) (Δ , τ)
ext ρ = Z ∷ suc-renaming ρ

_⟨_⟩ : Renaming Γ Δ → Γ ∋ τ → Δ ∋ τ
(x ∷ _) ⟨ Z ⟩ = x
(_ ∷ ρ) ⟨ S x ⟩ = ρ ⟨ x ⟩
   
_⟪_⟫ : Renaming Γ Δ → Γ ⊢ τ → Δ ⊢ τ
ρ ⟪ var x ⟫ = var (ρ ⟨ x ⟩)
ρ ⟪ s ∙ t ⟫ = ρ ⟪ s ⟫ ∙ ρ ⟪ t ⟫
ρ ⟪ abs t ⟫ = abs (ext ρ ⟪ t ⟫)

_◇_ : Renaming Γ Δ → Renaming Ω Γ → Renaming Ω Δ
ρ₁ ◇ ∅ = ∅
ρ₁ ◇ (x ∷ ρ₂) = ρ₁ ⟨ x ⟩ ∷ ρ₁ ◇ ρ₂

idᴿ : (Γ : Ctx) → Renaming Γ Γ
idᴿ ∅       = ∅
idᴿ (Γ , x) = ext (idᴿ Γ)
