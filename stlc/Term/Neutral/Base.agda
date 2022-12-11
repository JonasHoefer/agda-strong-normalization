{-# OPTIONS --safe --without-K #-}

open import Term
open import Term.StrongNormalization

module Term.Neutral.Base where

-- neutral terms: when applied, these terms do not create new redexes
-- these terms are strongly normalizing by definition as all reductions occur in the subterms that are already strongly normalizing
data NE : Γ ⊢ τ → Set where
  var : (x : Γ ∋ τ) → NE (var x)
  _∙_ : {t : Γ ⊢ τ₁ ⇒ τ₂} → NE t → {u : Γ ⊢ τ₁} → SN u → NE (t ∙ u)
