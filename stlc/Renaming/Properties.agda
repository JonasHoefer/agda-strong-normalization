{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂; cong-app; sym; trans; subst)
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Term
open import Renaming.Base

module Renaming.Properties where

renaming-extensionality : (ρ₁ ρ₂ : Renaming Γ Δ) → ((τ : Type) → (x : Γ ∋ τ) → ρ₁ ⟨ x ⟩ ≡ ρ₂ ⟨ x ⟩) → ρ₁ ≡ ρ₂
renaming-extensionality ∅         ∅         p = refl
renaming-extensionality (x₁ ∷ ρ₁) (x₂ ∷ ρ₂) p = cong₂ _∷_ (p _ Z) (renaming-extensionality ρ₁ ρ₂ λ τ x → p τ (S x))

suc-renaming-⟨-⟩ : (ρ : Renaming Γ Δ) (x : Γ ∋ τ) → suc-renaming {τ = τ₁} ρ ⟨ x ⟩ ≡ S (ρ ⟨ x ⟩)
suc-renaming-⟨-⟩ (x ∷ ρ) Z     = refl
suc-renaming-⟨-⟩ (_ ∷ ρ) (S x) = suc-renaming-⟨-⟩ ρ x

suc-renaming-◇ : (ρ₂ : Renaming Γ Δ) (ρ₁ : Renaming Ω Γ) → suc-renaming {τ = τ} (ρ₂ ◇ ρ₁) ≡ ext ρ₂ ◇ suc-renaming ρ₁
suc-renaming-◇ ρ₂ ∅ = refl
suc-renaming-◇ ρ₂ (x ∷ ρ₁) = cong₂ _∷_ (sym (suc-renaming-⟨-⟩ ρ₂ x)) (suc-renaming-◇ ρ₂ ρ₁)

ext-⟨-⟩ : (ρ : Renaming Γ Δ) (x : Γ ∋ τ) → ext {τ = τ₁} ρ ⟨ S x ⟩ ≡ suc-renaming ρ ⟨ x ⟩
ext-⟨-⟩ ρ Z     = refl
ext-⟨-⟩ ρ (S x) = refl

ext-id : (Γ : Ctx) → ext (idᴿ Γ) ≡ idᴿ (Γ , τ)
ext-id ∅       = refl
ext-id (Γ , x) = refl

ext-◇ : (ρ₂ : Renaming Γ Δ) (ρ₁ : Renaming Ω Γ) → ext {τ = τ} (ρ₂ ◇ ρ₁) ≡ ext ρ₂ ◇ ext ρ₁
ext-◇ ρ₂ ∅        = refl
ext-◇ ρ₂ (x ∷ ρ₁) = cong₂ _∷_ refl (cong₂ _∷_ (sym (suc-renaming-⟨-⟩ ρ₂ x)) (suc-renaming-◇ ρ₂ ρ₁))

rename-idⱽ : (x : Γ ∋ τ) → idᴿ Γ ⟨ x ⟩ ≡ x
rename-idⱽ Z = refl
rename-idⱽ (S x) = trans (suc-renaming-⟨-⟩ (idᴿ _) x) (cong S_ (rename-idⱽ x))

rename-id : (t : Γ ⊢ τ) → idᴿ Γ ⟪ t ⟫ ≡ t
rename-id (var x) = cong var (rename-idⱽ x)
rename-id (s ∙ t) = cong₂ _∙_ (rename-id s) (rename-id t)
rename-id (abs t) = cong abs (trans (cong (_⟪ t ⟫) (ext-id _)) (rename-id t))

rename-◇ⱽ : (ρ₂ : Renaming Δ Ω) (ρ₁ : Renaming Γ Δ) (x : Γ ∋ τ) → ρ₂ ◇ ρ₁ ⟨ x ⟩ ≡ ρ₂ ⟨ ρ₁ ⟨ x ⟩ ⟩
rename-◇ⱽ ρ₂ (x ∷ ρ₁) Z     = refl
rename-◇ⱽ ρ₂ (x ∷ ρ₁) (S y) = rename-◇ⱽ ρ₂ ρ₁ y

rename-◇ : (ρ₂ : Renaming Δ Ω) (ρ₁ : Renaming Γ Δ) (t : Γ ⊢ τ) → ρ₂ ◇ ρ₁ ⟪ t ⟫ ≡ ρ₂ ⟪ ρ₁ ⟪ t ⟫ ⟫
rename-◇ ρ₂ ρ₁ (var x) = cong var (rename-◇ⱽ ρ₂ ρ₁ x)
rename-◇ ρ₂ ρ₁ (s ∙ t) = cong₂ _∙_ (rename-◇ ρ₂ ρ₁ s) (rename-◇ ρ₂ ρ₁ t)
rename-◇ ρ₂ ρ₁ (abs t) = cong abs (trans ((cong (_⟪ t ⟫)) (ext-◇ ρ₂ ρ₁)) (rename-◇ (ext ρ₂) (ext ρ₁) t))

◇-identʳ : (ρ : Renaming Γ Δ) → ρ ◇ idᴿ _ ≡ ρ
◇-identʳ ρ = renaming-extensionality _ _ λ τ x → trans (rename-◇ⱽ ρ (idᴿ _) x) (cong (ρ ⟨_⟩) (rename-idⱽ x))

◇-identˡ : (ρ : Renaming Γ Δ) → idᴿ _ ◇ ρ ≡ ρ
◇-identˡ ρ = renaming-extensionality _ _ λ τ x → trans (rename-◇ⱽ (idᴿ _) ρ x) (rename-idⱽ (ρ ⟨ x ⟩))

suc-renaming≡comp-suc-id : (ρ : Renaming Γ Δ) → suc-renaming {τ = τ} ρ ≡ suc-renaming (idᴿ Δ) ◇ ρ
suc-renaming≡comp-suc-id ∅ = refl
suc-renaming≡comp-suc-id (x ∷ ρ) = cong₂ _∷_ (sym (trans (suc-renaming-⟨-⟩ (idᴿ _) x) (cong S_ (rename-idⱽ x)))) (suc-renaming≡comp-suc-id ρ)

suc-renaming-⟪-⟫ : (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → suc-renaming {τ = τ₁} ρ ⟪ t ⟫ ≡ suc-renaming (idᴿ Δ) ⟪ ρ ⟪ t ⟫ ⟫
suc-renaming-⟪-⟫ ρ t =
  begin
    suc-renaming ρ ⟪ t ⟫
  ≡⟨ cong (_⟪ t ⟫) (suc-renaming≡comp-suc-id ρ) ⟩
   suc-renaming (idᴿ _) ◇ ρ ⟪ t ⟫
  ≡⟨ rename-◇ (suc-renaming (idᴿ _)) ρ t ⟩
    suc-renaming (idᴿ _) ⟪ ρ ⟪ t ⟫ ⟫
  ∎

comm-renaming-weakeningⱽ : (ρ : Renaming Γ Δ) (x : Γ ∋ τ) → suc-renaming {τ = τ₁} (idᴿ Δ) ◇ ρ ⟨ x ⟩ ≡ ext ρ ◇ suc-renaming (idᴿ Γ) ⟨ x ⟩
comm-renaming-weakeningⱽ ρ x =
  begin
    suc-renaming (idᴿ _) ◇ ρ ⟨ x ⟩
  ≡⟨ rename-◇ⱽ (suc-renaming (idᴿ _)) ρ x ⟩
    suc-renaming (idᴿ _) ⟨ ρ ⟨ x ⟩ ⟩
  ≡⟨ suc-renaming-⟨-⟩ (idᴿ _) (ρ ⟨ x ⟩) ⟩
    S (idᴿ _ ⟨ ρ ⟨ x ⟩ ⟩)
  ≡⟨ cong S_ (rename-idⱽ (ρ ⟨ x ⟩)) ⟩
    (S (ρ ⟨ x ⟩) )
  ≡⟨ sym (suc-renaming-⟨-⟩ ρ x) ⟩
    suc-renaming ρ ⟨ x ⟩
  ≡⟨ ext-⟨-⟩ ρ x ⟩
    ext ρ ⟨ S x ⟩
  ≡⟨ sym (cong (λ - → ext ρ ⟨ S - ⟩) (rename-idⱽ x)) ⟩
    ext ρ ⟨ S (idᴿ _ ⟨ x ⟩) ⟩
  ≡⟨ sym (cong (ext ρ ⟨_⟩) (suc-renaming-⟨-⟩ (idᴿ _) x)) ⟩
    ext ρ ⟨ suc-renaming (idᴿ _) ⟨ x ⟩ ⟩
  ≡⟨ sym (rename-◇ⱽ (ext ρ) (suc-renaming (idᴿ _)) x) ⟩
    ext ρ ◇ suc-renaming (idᴿ _) ⟨ x ⟩
  ∎

comm-renaming-weakening : (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → suc-renaming {τ = τ₁} (idᴿ Δ) ⟪ ρ ⟪ t ⟫ ⟫ ≡ ext ρ ⟪ suc-renaming (idᴿ Γ) ⟪ t ⟫ ⟫
comm-renaming-weakening ρ t =
  begin
    suc-renaming (idᴿ _) ⟪ ρ ⟪ t ⟫ ⟫
  ≡⟨ sym (rename-◇ (suc-renaming (idᴿ _)) ρ t) ⟩
    suc-renaming (idᴿ _) ◇ ρ ⟪ t ⟫
  ≡⟨ cong (_⟪ t ⟫) (renaming-extensionality _ _ (λ _ → comm-renaming-weakeningⱽ ρ)) ⟩
    ext ρ ◇ suc-renaming (idᴿ _) ⟪ t ⟫
  ≡⟨ rename-◇ (ext ρ) (suc-renaming (idᴿ _)) t ⟩
    ext ρ ⟪ suc-renaming (idᴿ _) ⟪ t ⟫ ⟫
  ∎
