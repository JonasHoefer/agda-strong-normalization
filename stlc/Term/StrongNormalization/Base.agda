{-# OPTIONS --safe --without-K #-}

open import Term
open import Reduction

module Term.StrongNormalization.Base where

-- Strongly normalizing terms, i.e., those terms from which all reduction chains are finite
data SN : Γ ⊢ τ → Set where
  sn : {t : Γ ⊢ τ} → (∀ s → t ▷ s → SN s) → SN t

-- multi step strong normalization, sometimes needed for Agda to see termination
data SN⁺ : Γ ⊢ τ → Set where
  sn : {t : Γ ⊢ τ} → (∀ s → t ▷⁺ s → SN⁺ s) → SN⁺ t
