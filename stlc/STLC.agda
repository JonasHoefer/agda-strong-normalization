{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂; cong-app; sym; trans; subst)
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to _,ˣ_)

open import Function using (case_of_)

open import Term
open import Term.StrongNormalization
open import Term.Neutral
open import Renaming
open import Substitution
open import Reduction

module STLC where

-- The logical predicate for strong normalization.
-- It is defined by induction on the type, allowing us to induce on the type of terms which satisfy the predicate,
-- and is closed under application by definition.
⟦_∶_⟧ : (Γ : Ctx) (τ : Type) → Γ ⊢ τ → Set
⟦ Γ ∶ ⋆ ⟧     t = SN t
⟦ Γ ∶ τ ⇒ σ ⟧ t = {Δ : Ctx} (ρ : Renaming Γ Δ) (u : Δ ⊢ τ) → ⟦ Δ ∶ τ ⟧ u → ⟦ Δ ∶ σ ⟧ (ρ ⟪ t ⟫ ∙ u)

-- Its extension to contexts
⟦_⟧ : (Γ : Ctx) {Δ : Ctx} → Subst Γ Δ → Set
⟦ Γ ⟧ {Δ = Δ} σ = {τ : Type} (x : Γ ∋ τ) → ⟦ Δ ∶ τ ⟧ (σ ⟨ x ⟩ˢ)


-- ⟦-∶-⟧ also interacts with renamings as one would expect
renaming-⟦_∶_⟧ : (Γ : Ctx) (τ : Type) (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → ⟦ Γ ∶ τ ⟧ t → ⟦ Δ ∶ τ ⟧ (ρ ⟪ t ⟫)
renaming-⟦ Γ ∶ ⋆ ⟧ ρ t t∈SN = renaming-SN ρ t t∈SN
renaming-⟦ Γ ∶ τ₁ ⇒ τ₂ ⟧ ρ t t∈⟦Γ∶τ₁⇒τ₂⟧ ρ₁ u u∈⟦Δ:τ₁⟧ = subst (λ - → ⟦ _ ∶ _ ⟧ (- ∙ u)) (rename-◇ ρ₁ ρ t) (t∈⟦Γ∶τ₁⇒τ₂⟧ (ρ₁ ◇ ρ) u u∈⟦Δ:τ₁⟧)

--------------------------------------------------------------------------------
---- NE ⊆ ⟦ Γ ∶ τ ⟧ ⊆ SN

-- we show that the predicate solves our problem, i.e., terms satisfying the predicate are strongly normalizing
-- we proof the inclusions by mutual induction over the type, proving at the same time that all neutral terms satisfy the predicate
⟦_∶_⟧⊆SN : (Γ : Ctx) (τ : Type) (t : Γ ⊢ τ) → ⟦ Γ ∶ τ ⟧ t → SN t
NE⊆⟦_∶_⟧ : (Γ : Ctx) (τ : Type) (t : Γ ⊢ τ) → NE t → ⟦ Γ ∶ τ ⟧ t

-- for the base type ⋆ the statement is trivial as ⟦⋆⟧ = SN by definition and NE are always strongly normalizing essentially by construction

⟦ Γ ∶ ⋆ ⟧⊆SN t t∈SN = t∈SN
⟦ Γ ∶ τ₁ ⇒ τ₂ ⟧⊆SN t t∈⟦τ₁⇒τ₂⟧ = SN-renaming (suc-renaming (idᴿ Γ)) t ρt∈SN
  where
    tx∈⟦Γ,τ₁∶τ₂⟧ : ⟦ Γ , τ₁ ∶ τ₂ ⟧ (suc-renaming (idᴿ Γ) ⟪ t ⟫ ∙ var Z)
    tx∈⟦Γ,τ₁∶τ₂⟧ = t∈⟦τ₁⇒τ₂⟧ (suc-renaming (idᴿ Γ)) (var Z) (NE⊆⟦ Γ , τ₁ ∶ τ₁ ⟧ (var Z) (var Z))

    ρtx∈SN : SN (suc-renaming (idᴿ Γ) ⟪ t ⟫ ∙ var Z)
    ρtx∈SN = ⟦ (Γ , τ₁) ∶ τ₂ ⟧⊆SN (suc-renaming (idᴿ Γ) ⟪ t ⟫ ∙ var Z) tx∈⟦Γ,τ₁∶τ₂⟧

    ρt∈SN : SN (suc-renaming (idᴿ Γ) ⟪ t ⟫)
    ρt∈SN = tu∈SN⇒t∈SN _ _ ρtx∈SN

NE⊆⟦ Γ ∶ ⋆ ⟧ t t∈NE = NE⊆SN t t∈NE
-- Since we induce over the type, we can use the induction hypothesis for this case, and thus have to show that ρt∙u is neutral.
-- (The term gets larger but the type smaller!) t is already neutral. To show that u is strongly normalizing, we use the IH and
-- that u satisfies the logical predicate.
--
-- Due to our definition of types, we have to handle the application of terms in a larger context, this follows easily.
NE⊆⟦ Γ ∶ τ₁ ⇒ τ₂ ⟧ t t∈NE ρ u u∈⟦Δ∶τ₂⟧ = NE⊆⟦ _ ∶ τ₂ ⟧ (ρ ⟪ t ⟫ ∙ u) (renaming-NE ρ t t∈NE ∙ ⟦ _ ∶ τ₁ ⟧⊆SN u u∈⟦Δ∶τ₂⟧)


--------------------------------------------------------------------------------
---- id∈⟦Γ⟧

-- An immediate consequence is that the identity substitution satisfies the predicate.
id∈⟦Γ⟧ : (Γ : Ctx) → ⟦ Γ ⟧ (idˢ Γ)
id∈⟦Γ⟧ Γ x = subst ⟦ Γ ∶ _ ⟧ (sym (subst-id (var x))) (NE⊆⟦ Γ ∶ _ ⟧ (var x) (var x))


--------------------------------------------------------------------------------
---- ⟦_∶_⟧ closed under β expansion

-- We prove a more general fact from which we can conclude the closure under β expansion.
⟦_∶_⟧-closed-backwards-▷ʷ : (Γ : Ctx) (τ : Type) (t t′ : Γ ⊢ τ) → ⟦ Γ ∶ τ ⟧ t′ → t ▷ʷ t′ → SN t → ⟦ Γ ∶ τ ⟧ t
⟦ Γ ∶ ⋆ ⟧-closed-backwards-▷ʷ t t′ t′∈⟦Γ∶τ⟧ t▷ʷt′ t∈SN = t∈SN
⟦ Γ ∶ τ₁ ⇒ τ₂ ⟧-closed-backwards-▷ʷ t t′ t′∈⟦Γ∶τ₁⇒τ₂⟧ t▷ʷt′ t∈SN ρ u u∈⟦Δ∶τ₁⟧ =
  ⟦ _ ∶ τ₂ ⟧-closed-backwards-▷ʷ (ρ ⟪ t ⟫ ∙ u) (ρ ⟪ t′ ⟫ ∙ u) (t′∈⟦Γ∶τ₁⇒τ₂⟧ ρ u u∈⟦Δ∶τ₁⟧) (ξ₁ (rename-▷ʷ ρ t▷ʷt′))
    (SN-closed-backwards-▷ʷ (ρ ⟪ t ⟫) (ρ ⟪ t′ ⟫) u (renaming-SN ρ t t∈SN) (⟦ _ ∶ τ₂ ⟧⊆SN (ρ ⟪ t′ ⟫ ∙ u) (t′∈⟦Γ∶τ₁⇒τ₂⟧ ρ u u∈⟦Δ∶τ₁⟧)) (rename-▷ʷ ρ t▷ʷt′))

⟦-⟧-closed-β-expansion : (t : Γ , τ₁ ⊢ τ₂) (u : Γ ⊢ τ₁) → SN u → ⟦ Γ ∶ τ₂ ⟧ (t [ u ]) → ⟦ Γ ∶ τ₂ ⟧ (abs t ∙ u)
⟦-⟧-closed-β-expansion t u u∈SN t[u]∈⟦Γ∶τ₂⟧ = ⟦ _ ∶ _ ⟧-closed-backwards-▷ʷ (abs t ∙ u) (t [ u ]) t[u]∈⟦Γ∶τ₂⟧ β
  (SN-closed-β-expansion t u (SN⊆SN⁺ (⟦ _ ∶ _ ⟧⊆SN (t [ u ]) t[u]∈⟦Γ∶τ₂⟧)) u∈SN)


--------------------------------------------------------------------------------
---- Fundamental theorem for ⟦_⟧

theorem : (t : Γ ⊢ τ) (σ : Subst Γ Δ) → ⟦ Γ ⟧ σ → ⟦ Δ ∶ τ ⟧ (σ ⟪ t ⟫ˢ)
theorem (var x) σ σ∈⟦Γ⟧ = σ∈⟦Γ⟧ x
theorem (s ∙ t) σ σ∈⟦Γ⟧ = subst (λ - → ⟦ _ ∶ _ ⟧ (- ∙ _)) (rename-id (σ ⟪ s ⟫ˢ)) (theorem s σ σ∈⟦Γ⟧ (idᴿ _) (σ ⟪ t ⟫ˢ) (theorem t σ σ∈⟦Γ⟧))
theorem (abs t) σ σ∈⟦Γ⟧ ρ u u∈⟦Δ∶τ₁⟧ = ⟦-⟧-closed-β-expansion (ext ρ ⟪ exts σ ⟪ t ⟫ˢ ⟫) u (⟦ _ ∶ _ ⟧⊆SN u u∈⟦Δ∶τ₁⟧) σ′t∈⟦-∶-⟧
  where
    σ′ : Subst _ _
    σ′ = substOuter u ◆ exts (ρ ⬖ σ)

    -- σ′ substitutes non-zero vars as a renamed version of σ
    σ′-suc : (x : _ ∋ τ) → ρ ⟪ σ ⟨ x ⟩ˢ ⟫ ≡ σ′ ⟨ S x ⟩ˢ
    σ′-suc x = trans (sym (subst-⬖ ρ σ (var x))) (subst-outer-abs-suc-subst (ρ ⬖ σ) u x)

    -- Thus, we can conclude that σ′ ∈ ⟦Γ , τ₁⟧ because u satisfies the predicate and σ does as well.
    σ′∈⟦Γ⟧ : ⟦ _ ⟧ σ′
    σ′∈⟦Γ⟧ Z     = u∈⟦Δ∶τ₁⟧
    σ′∈⟦Γ⟧ (S x) = subst ⟦ _ ∶ _ ⟧ (σ′-suc x) (renaming-⟦ _ ∶ _ ⟧ ρ (σ ⟨ x ⟩ˢ) (σ∈⟦Γ⟧ x))

    σ′-ident : σ′ ⟪ t ⟫ˢ ≡ (ext ρ ⟪ exts σ ⟪ t ⟫ˢ ⟫ [ u ])
    σ′-ident =
      begin
        substOuter u ◆ exts (ρ ⬖ σ) ⟪ t ⟫ˢ
      ≡⟨ cong (λ - → substOuter u ◆ - ⟪ t ⟫ˢ) (exts-⬖ ρ σ) ⟩
        substOuter u ◆ (ext ρ ⬖ exts σ) ⟪ t ⟫ˢ
      ≡⟨ subst-◆ (substOuter u) (ext ρ ⬖ exts σ) t ⟩
        substOuter u ⟪ ext ρ ⬖ exts σ ⟪ t ⟫ˢ ⟫ˢ
      ≡⟨ cong (substOuter u ⟪_⟫ˢ) (subst-⬖ (ext ρ) (exts σ) t) ⟩
        substOuter u ⟪ ext ρ ⟪ (exts σ) ⟪ t ⟫ˢ ⟫ ⟫ˢ
      ∎

    σ′t∈⟦-∶-⟧ : ⟦ _ ∶ _ ⟧ (ext ρ ⟪ exts σ ⟪ t ⟫ˢ ⟫ [ u ])
    σ′t∈⟦-∶-⟧ = subst ⟦ _ ∶ _ ⟧ σ′-ident (theorem t σ′ σ′∈⟦Γ⟧)


--------------------------------------------------------------------------------
---- STLC is strongly normalizing

t∈SN : (t : Γ ⊢ τ) → SN t
t∈SN t = subst SN (subst-id t) (⟦ _ ∶ _ ⟧⊆SN _ (theorem t (idˢ _) (id∈⟦Γ⟧ _)))
