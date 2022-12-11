{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂; cong-app; sym; trans; subst)
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Term
open import Renaming
open import Substitution.Base

module Substitution.Properties where

variable σ σ₁ σ₂ : Subst Γ Δ

--------------------------------------------------------------------------------
---- Basic Properties                                                       ----
--------------------------------------------------------------------------------

subst-extensionality : (σ₁ σ₂ : Subst Γ Δ) → ((τ : Type) → (x : Γ ∋ τ) → σ₁ ⟨ x ⟩ˢ ≡ σ₂ ⟨ x ⟩ˢ) → σ₁ ≡ σ₂
subst-extensionality ∅ ∅ x = refl
subst-extensionality (x₁ ∷ σ₁) (x₂ ∷ σ₂) p = cong₂ _∷_ (p _ Z) (subst-extensionality σ₁ σ₂ λ _ x → p _ (S x))

subst-ext-var : (σ₁ σ₂ : Subst Γ Δ) → ((τ : Type) → (x : Γ ∋ τ) → σ₁ ⟨ x ⟩ˢ ≡ σ₂ ⟨ x ⟩ˢ) → (t : Γ ⊢ τ) → σ₁ ⟪ t ⟫ˢ ≡ σ₂ ⟪ t ⟫ˢ
subst-ext-var σ₁ σ₂ p t = cong (_⟪ t ⟫ˢ) (subst-extensionality σ₁ σ₂ p)

suc-subst-⟨-⟩ˢ : (σ : Subst Γ Δ) (x : Γ ∋ τ) → suc-subst {τ = τ₁} σ ⟨ x ⟩ˢ ≡ suc-renaming (idᴿ _) ⟪ σ ⟨ x ⟩ˢ ⟫
suc-subst-⟨-⟩ˢ (t ∷ σ) Z     = refl
suc-subst-⟨-⟩ˢ (_ ∷ σ) (S x) = suc-subst-⟨-⟩ˢ σ x


--------------------------------------------------------------------------------
---- Properties of Lift                                                     ----
--------------------------------------------------------------------------------

lift-⟨-⟩ˢ : (ρ : Renaming Γ Δ) (x : Γ ∋ τ) → lift ρ ⟨ x ⟩ˢ ≡ var (ρ ⟨ x ⟩)
lift-⟨-⟩ˢ (x ∷ ρ) Z     = refl
lift-⟨-⟩ˢ (x ∷ ρ) (S y) = lift-⟨-⟩ˢ ρ y

suc-lift : (ρ : Renaming Γ Δ) → suc-subst {τ = τ} (lift ρ) ≡ lift (suc-renaming ρ)
suc-lift ∅ = refl
suc-lift (x ∷ ρ) = cong₂ _∷_ (cong var (trans (suc-renaming-⟨-⟩ (idᴿ _) x) (cong S_ (rename-idⱽ x)))) (suc-lift ρ)

exts-lift : (ρ : Renaming Γ Δ) → exts {τ = τ} (lift ρ) ≡ lift (ext ρ)
exts-lift ∅ = refl
exts-lift (x ∷ ρ) = cong (var Z ∷_) (cong₂ _∷_ (cong var (trans (suc-renaming-⟨-⟩ (idᴿ _) x) (cong S_ (rename-idⱽ x)))) (suc-lift ρ))

lift-⟪-⟫ˢ : (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → lift ρ ⟪ t ⟫ˢ ≡ ρ ⟪ t ⟫
lift-⟪-⟫ˢ ρ (var x) = lift-⟨-⟩ˢ ρ x
lift-⟪-⟫ˢ ρ (s ∙ t) = cong₂ _∙_ (lift-⟪-⟫ˢ ρ s) (lift-⟪-⟫ˢ ρ t)
lift-⟪-⟫ˢ ρ (abs t) = cong abs (trans (cong (_⟪ t ⟫ˢ) (exts-lift ρ)) (lift-⟪-⟫ˢ (ext ρ) t))

lift-⬗ : (σ : Subst Δ Ω) (ρ : Renaming Γ Δ) → σ ⬗ ρ ≡ σ ◆ lift ρ
lift-⬗ σ ∅       = refl
lift-⬗ σ (x ∷ ρ) = cong₂ _∷_ refl (lift-⬗ σ ρ)

lift-⬖ : (ρ : Renaming Δ Ω) (σ : Subst Γ Δ) → ρ ⬖ σ ≡ lift ρ ◆ σ
lift-⬖ ρ ∅       = refl
lift-⬖ ρ (x ∷ σ) = cong₂ _∷_ (sym (lift-⟪-⟫ˢ ρ x)) (lift-⬖ ρ σ)

lift-id : (Γ : Ctx) → lift (idᴿ Γ) ≡ idˢ Γ
lift-id ∅ = refl
lift-id (Γ , x) = cong (var Z ∷_) (trans (sym (suc-lift (idᴿ Γ))) (cong suc-subst (lift-id Γ)))

--------------------------------------------------------------------------------
---- Mixed Version Left                                                     ----
--------------------------------------------------------------------------------

subst-⬖ⱽ : (ρ : Renaming Δ Ω) (σ : Subst Γ Δ) (x : Γ ∋ τ) → ρ ⬖ σ ⟨ x ⟩ˢ ≡ ρ ⟪ σ ⟨ x ⟩ˢ ⟫
subst-⬖ⱽ ρ (x ∷ σ) Z     = refl
subst-⬖ⱽ ρ (x ∷ σ) (S y) = subst-⬖ⱽ ρ σ y

suc-subst-⬖ : (ρ : Renaming Δ Ω) (σ : Subst Γ Δ) → suc-subst {τ = τ} (ρ ⬖ σ) ≡ ext ρ ⬖ suc-subst σ
suc-subst-⬖ ρ ∅ = refl
suc-subst-⬖ ρ (x ∷ σ) = cong₂ _∷_ (comm-renaming-weakening ρ x) (suc-subst-⬖ ρ σ)

exts-⬖ : (ρ : Renaming Δ Ω) (σ : Subst Γ Δ) → exts {τ = τ} (ρ ⬖ σ) ≡ ext ρ ⬖ exts σ
exts-⬖ ρ ∅ = refl
exts-⬖ ρ (x ∷ σ) = cong (var Z ∷_) (cong₂ _∷_ (comm-renaming-weakening ρ x) (suc-subst-⬖ ρ σ))

subst-⬖ : (ρ : Renaming Δ Ω) (σ : Subst Γ Δ) (t : Γ ⊢ τ) → ρ ⬖ σ ⟪ t ⟫ˢ ≡ ρ ⟪ σ ⟪ t ⟫ˢ ⟫
subst-⬖ ρ σ (var x) = subst-⬖ⱽ ρ σ x
subst-⬖ ρ σ (s ∙ t) = cong₂ _∙_ (subst-⬖ ρ σ s) (subst-⬖ ρ σ t)
subst-⬖ ρ σ (abs t) = cong abs (trans (cong (_⟪ t ⟫ˢ) (exts-⬖ ρ σ)) (subst-⬖ (ext ρ) (exts σ) t))


--------------------------------------------------------------------------------
---- Mixed Version Right                                                    ----
--------------------------------------------------------------------------------

subst-⬗ⱽ : (σ : Subst Δ Ω) (ρ : Renaming Γ Δ) (x : Γ ∋ τ) → σ ⬗ ρ ⟨ x ⟩ˢ ≡ σ ⟨ ρ ⟨ x ⟩ ⟩ˢ
subst-⬗ⱽ σ (x ∷ ρ) Z     = refl
subst-⬗ⱽ σ (x ∷ ρ) (S y) = subst-⬗ⱽ σ ρ y

suc-subst-⬗ : (σ : Subst Δ Ω) (ρ : Renaming Γ Δ) → suc-subst {τ = τ} (σ ⬗ ρ) ≡ exts σ ⬗ suc-renaming ρ
suc-subst-⬗ σ ∅ = refl
suc-subst-⬗ σ (x ∷ ρ) = cong₂ _∷_ (sym (suc-subst-⟨-⟩ˢ σ x)) (suc-subst-⬗ σ ρ)

exts-⬗ : (σ : Subst Δ Ω) (ρ : Renaming Γ Δ) → exts {τ = τ} (σ ⬗ ρ) ≡ exts σ ⬗ ext ρ
exts-⬗ σ ∅ = refl
exts-⬗ σ (x ∷ ρ) = cong (var Z ∷_) (cong₂ _∷_ (sym (suc-subst-⟨-⟩ˢ σ x)) (suc-subst-⬗ σ ρ))

subst-⬗ : (σ : Subst Δ Ω) (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → σ ⬗ ρ ⟪ t ⟫ˢ ≡ σ ⟪ ρ ⟪ t ⟫ ⟫ˢ
subst-⬗ σ ρ (var x) = subst-⬗ⱽ σ ρ x
subst-⬗ σ ρ (s ∙ t) = cong₂ _∙_ (subst-⬗ σ ρ s) (subst-⬗ σ ρ t)
subst-⬗ σ ρ (abs t) = cong abs (trans (cong _⟪ t ⟫ˢ (exts-⬗ σ ρ)) (subst-⬗ (exts σ) (ext ρ) t))


--------------------------------------------------------------------------------
---- Mixed Versions Interaction                                             ----
--------------------------------------------------------------------------------

ren⬖σ≡σ⬗ren : (σ : Subst Γ Δ) (x : Γ ∋ τ) → suc-renaming {τ = τ₁} (idᴿ Δ) ⬖ σ ⟨ x ⟩ˢ ≡ exts σ ⬗ suc-renaming (idᴿ Γ) ⟨ x ⟩ˢ
ren⬖σ≡σ⬗ren σ x =
  begin
    suc-renaming (idᴿ _) ⬖ σ ⟨ x ⟩ˢ
  ≡⟨ subst-⬖ⱽ (suc-renaming (idᴿ _)) σ x ⟩
    suc-renaming (idᴿ _) ⟪ σ ⟨ x ⟩ˢ ⟫
  ≡⟨ sym (suc-subst-⟨-⟩ˢ σ x) ⟩
    (suc-subst σ ⟨ x ⟩ˢ)
  ≡⟨⟩
    (exts σ ⟨ S x ⟩ˢ)
  ≡⟨ cong (λ - → exts σ ⟨ S - ⟩ˢ) (sym (rename-idⱽ x)) ⟩
    (exts σ ⟨ S (idᴿ _ ⟨ x ⟩) ⟩ˢ)
  ≡⟨ cong (exts σ ⟨_⟩ˢ) (sym (suc-renaming-⟨-⟩ (idᴿ _) x)) ⟩
    exts σ ⟨ suc-renaming (idᴿ _) ⟨ x ⟩ ⟩ˢ
  ≡⟨ sym (subst-⬗ⱽ (exts σ) (suc-renaming (idᴿ _)) x) ⟩
    exts σ ⬗ suc-renaming (idᴿ _) ⟨ x ⟩ˢ
  ∎

ren⟪σ⟪t⟫ˢ⟫≡σ⟪ren⟪t⟫⟫ˢ : (σ : Subst Γ Δ) (t : Γ ⊢ τ) → suc-renaming {τ = τ₁} (idᴿ _) ⟪ σ ⟪ t ⟫ˢ ⟫ ≡ exts σ ⟪ suc-renaming (idᴿ _) ⟪ t ⟫ ⟫ˢ
ren⟪σ⟪t⟫ˢ⟫≡σ⟪ren⟪t⟫⟫ˢ σ t = begin
    suc-renaming (idᴿ _) ⟪ σ ⟪ t ⟫ˢ ⟫
  ≡⟨ sym (subst-⬖ (suc-renaming (idᴿ _)) σ t) ⟩
    (suc-renaming (idᴿ _) ⬖ σ) ⟪ t ⟫ˢ
  ≡⟨ cong (_⟪ t ⟫ˢ) (subst-extensionality _ _ λ _ → ren⬖σ≡σ⬗ren σ) ⟩
    exts σ ⬗ suc-renaming (idᴿ _) ⟪ t ⟫ˢ
  ≡⟨ subst-⬗ (exts σ) (suc-renaming (idᴿ _)) t ⟩
    exts σ ⟪ suc-renaming (idᴿ _) ⟪ t ⟫ ⟫ˢ
  ∎

--------------------------------------------------------------------------------
---- Properties of Substitution                                             ----
--------------------------------------------------------------------------------

suc-subst-◆ : (σ₂ : Subst Γ Δ) (σ₁ : Subst Ω Γ) → suc-subst {τ = τ} (σ₂ ◆ σ₁) ≡ exts σ₂ ◆ suc-subst σ₁
suc-subst-◆ σ₂ ∅        = refl
suc-subst-◆ σ₂ (t ∷ σ₁) = cong₂ _∷_ (ren⟪σ⟪t⟫ˢ⟫≡σ⟪ren⟪t⟫⟫ˢ σ₂ t) (suc-subst-◆ σ₂ σ₁)

exts-id : (Γ : Ctx) → exts (idˢ Γ) ≡ idˢ (Γ , τ)
exts-id ∅       = refl
exts-id (Γ , _) = refl

ext-◆ : (σ₂ : Subst Γ Δ) (σ₁ : Subst Ω Γ) → exts {τ = τ} (σ₂ ◆ σ₁) ≡ exts σ₂ ◆ exts σ₁
ext-◆ σ₂ ∅        = refl
ext-◆ σ₂ (t ∷ σ₁) = cong₂ _∷_ refl (cong₂ _∷_ (ren⟪σ⟪t⟫ˢ⟫≡σ⟪ren⟪t⟫⟫ˢ σ₂ t) (suc-subst-◆ σ₂ σ₁))

subst-idⱽ : (x : Γ ∋ τ) → idˢ Γ ⟨ x ⟩ˢ ≡ var x
subst-idⱽ Z     = refl
subst-idⱽ (S x) =
  begin
    (suc-subst (idˢ _) ⟨ x ⟩ˢ)
  ≡⟨ suc-subst-⟨-⟩ˢ (idˢ _) x ⟩
    suc-renaming (idᴿ _) ⟪ idˢ _ ⟨ x ⟩ˢ ⟫
  ≡⟨ cong (λ - → suc-renaming (idᴿ _) ⟪ - ⟫) (subst-idⱽ x) ⟩
    suc-renaming (idᴿ _) ⟪ var x ⟫
  ≡⟨ cong var ((suc-renaming-⟨-⟩ (idᴿ _) x)) ⟩
    var (S (idᴿ _ ⟨ x ⟩))
  ≡⟨ cong (λ - → var (S -)) (rename-idⱽ x) ⟩
    var (S x)
  ∎

subst-id : (t : Γ ⊢ τ) → idˢ Γ ⟪ t ⟫ˢ ≡ t
subst-id (var x) = subst-idⱽ x
subst-id (s ∙ t) = cong₂ _∙_ (subst-id s) (subst-id t)
subst-id (abs t) = cong abs (trans (cong (_⟪ t ⟫ˢ) (exts-id _)) (subst-id t))

subst-◆ⱽ : (σ₂ : Subst Δ Ω) (σ₁ : Subst Γ Δ) (x : Γ ∋ τ) → σ₂ ◆ σ₁ ⟨ x ⟩ˢ ≡ σ₂ ⟪ σ₁ ⟨ x ⟩ˢ ⟫ˢ
subst-◆ⱽ σ₂ (t ∷ σ₁) Z     = refl
subst-◆ⱽ σ₂ (t ∷ σ₁) (S x) = subst-◆ⱽ σ₂ σ₁ x

subst-◆ : (σ₂ : Subst Δ Ω) (σ₁ : Subst Γ Δ) (t : Γ ⊢ τ) → σ₂ ◆ σ₁ ⟪ t ⟫ˢ ≡ σ₂ ⟪ σ₁ ⟪ t ⟫ˢ ⟫ˢ
subst-◆ σ₂ σ₁ (var x) = subst-◆ⱽ σ₂ σ₁ x
subst-◆ σ₂ σ₁ (s ∙ t) = cong₂ _∙_ (subst-◆ σ₂ σ₁ s) (subst-◆ σ₂ σ₁ t)
subst-◆ σ₂ σ₁ (abs t) = cong abs (trans ((cong (_⟪ t ⟫ˢ)) (ext-◆ σ₂ σ₁)) (subst-◆ (exts σ₂) (exts σ₁) t))

suc-subst-⟨-⟩ˢ-⬖ : (σ : Subst Γ Δ) (x : Γ ∋ τ) → suc-subst {τ = τ₁} σ ⟨ x ⟩ˢ ≡ suc-renaming (idᴿ Δ) ⬖ σ ⟨ x ⟩ˢ
suc-subst-⟨-⟩ˢ-⬖ (x ∷ σ) Z     = refl
suc-subst-⟨-⟩ˢ-⬖ (x ∷ σ) (S y) = suc-subst-⟨-⟩ˢ-⬖ σ y

exts-⟪-⟫ˢ : (σ : Subst Γ Δ) (t : Γ , τ₂ ⊢ τ₁) → exts (suc-subst {τ = τ} σ) ⟪ t ⟫ˢ ≡ ext (suc-renaming (idᴿ _)) ⟪ exts σ ⟪ t ⟫ˢ ⟫
exts-⟪-⟫ˢ σ t =
  begin
    exts (suc-subst σ) ⟪ t ⟫ˢ
  ≡⟨ cong (λ - → exts - ⟪ t ⟫ˢ) (subst-extensionality _ _ (λ _ x → trans (suc-subst-⟨-⟩ˢ σ x) (sym (subst-⬖ (suc-renaming (idᴿ _)) σ (var x))))) ⟩
    exts (suc-renaming (idᴿ _) ⬖ σ) ⟪ t ⟫ˢ
  ≡⟨ cong (_⟪ t ⟫ˢ) (exts-⬖ (suc-renaming (idᴿ _)) σ) ⟩
    ext (suc-renaming (idᴿ _)) ⬖ exts σ ⟪ t ⟫ˢ
  ≡⟨ subst-⬖ (ext (suc-renaming (idᴿ _))) (exts σ) t ⟩
    ext (suc-renaming (idᴿ _)) ⟪ exts σ ⟪ t ⟫ˢ ⟫
  ∎

suc-subst-⟪-⟫ˢ : (σ : Subst Γ Δ) (t : Γ ⊢ τ) → suc-subst {τ = τ₁} σ ⟪ t ⟫ˢ ≡ suc-renaming (idᴿ _) ⟪ σ ⟪ t ⟫ˢ ⟫
suc-subst-⟪-⟫ˢ σ (var x) = suc-subst-⟨-⟩ˢ σ x
suc-subst-⟪-⟫ˢ σ (s ∙ t) = cong₂ _∙_ (suc-subst-⟪-⟫ˢ σ s) (suc-subst-⟪-⟫ˢ σ t)
suc-subst-⟪-⟫ˢ σ (abs t) = cong abs (exts-⟪-⟫ˢ σ t)

◆-identʳ : (σ : Subst Γ Δ) → σ ◆ idˢ _ ≡ σ
◆-identʳ σ = subst-extensionality _ _ λ τ x →
  begin
    σ ◆ idˢ _ ⟨ x ⟩ˢ
  ≡⟨ subst-◆ⱽ σ (idˢ _) x ⟩
    σ ⟪ idˢ _ ⟨ x ⟩ˢ ⟫ˢ
  ≡⟨ cong (σ ⟪_⟫ˢ) (subst-id (var x)) ⟩
    σ ⟨ x ⟩ˢ
  ∎

⬖-identʳ : (ρ : Renaming Γ Δ) → ρ ⬖ idˢ _ ≡ lift ρ
⬖-identʳ ρ = trans (lift-⬖ ρ (idˢ _)) (◆-identʳ (lift ρ))

◆-identˡ : (σ : Subst Γ Δ) → idˢ _ ◆ σ ≡ σ
◆-identˡ σ = subst-extensionality _ _ λ τ x →
  begin
    idˢ _ ◆ σ ⟨ x ⟩ˢ
  ≡⟨ subst-◆ⱽ (idˢ _) σ x ⟩
    idˢ _ ⟪ σ ⟨ x ⟩ˢ ⟫ˢ
  ≡⟨ subst-id (σ ⟨ x ⟩ˢ) ⟩
    σ ⟨ x ⟩ˢ
  ∎


--------------------------------------------------------------------------------
---- Properties of -[-]                                                     ----
--------------------------------------------------------------------------------

-- because we shift the vars by 1, the substOuter has no effect
subst-outer-abs-suc-renaming : (ρ : Renaming Γ Δ) (t : Δ ⊢ τ₁) (x : Γ ∋ τ₂) → lift ρ ⟨ x ⟩ˢ ≡ substOuter t ⬗ suc-renaming ρ ⟨ x ⟩ˢ
subst-outer-abs-suc-renaming ρ t x = begin
    lift ρ ⟨ x ⟩ˢ
  ≡⟨ lift-⟨-⟩ˢ ρ x ⟩
    var (ρ ⟨ x ⟩)
  ≡⟨ sym (subst-id (var (ρ ⟨ x ⟩))) ⟩
    (t ∷ idˢ _) ⟨ S (ρ ⟨ x ⟩) ⟩ˢ
  ≡⟨ sym (cong ((t ∷ idˢ _) ⟨_⟩ˢ) (suc-renaming-⟨-⟩ ρ x)) ⟩
    (t ∷ idˢ _) ⟨ suc-renaming ρ ⟨ x ⟩ ⟩ˢ
  ≡⟨ sym (subst-⬗ (t ∷ idˢ _) (suc-renaming ρ) (var x)) ⟩
    (t ∷ idˢ _) ⬗ suc-renaming ρ ⟨ x ⟩ˢ
  ∎

subst-outer-abs-suc-subst : (σ : Subst Γ Δ) (t : Δ ⊢ τ₁) (x : Γ ∋ τ₂) → σ ⟨ x ⟩ˢ ≡ substOuter t ◆ suc-subst σ ⟨ x ⟩ˢ
subst-outer-abs-suc-subst σ t x =
  begin
    σ ⟨ x ⟩ˢ
  ≡⟨ sym (subst-id (σ ⟨ x ⟩ˢ)) ⟩
    idˢ _ ⟪ σ ⟨ x ⟩ˢ ⟫ˢ
  ≡⟨ cong _⟪ σ ⟨ x ⟩ˢ ⟫ˢ (sym (lift-id _)) ⟩
    lift (idᴿ _) ⟪ σ ⟨ x ⟩ˢ ⟫ˢ
  ≡⟨ subst-ext-var _ _ (λ τ → subst-outer-abs-suc-renaming (idᴿ _) t) (σ ⟨ x ⟩ˢ) ⟩
    substOuter t ⬗ suc-renaming (idᴿ _) ⟪ σ ⟨ x ⟩ˢ ⟫ˢ
  ≡⟨ subst-⬗ (substOuter t) (suc-renaming (idᴿ _)) (σ ⟨ x ⟩ˢ) ⟩
    substOuter t ⟪ suc-renaming (idᴿ _) ⟪ σ ⟨ x ⟩ˢ ⟫ ⟫ˢ
  ≡⟨ sym (cong (substOuter t ⟪_⟫ˢ) (suc-subst-⟨-⟩ˢ σ x)) ⟩
    substOuter t ⟪ suc-subst σ ⟨ x ⟩ˢ ⟫ˢ
  ≡⟨ sym (subst-◆ (substOuter t) (suc-subst σ) (var x)) ⟩
    substOuter t ◆ suc-subst σ ⟨ x ⟩ˢ
  ∎

rename-[] : (t : Γ , τ₁ ⊢ τ₂) (s : Γ ⊢ τ₁) (ρ : Renaming Γ Δ) → ρ ⟪ t [ s ] ⟫ ≡ ext ρ ⟪ t ⟫ [ ρ ⟪ s ⟫ ]
rename-[] t s ρ =
  begin
    ρ ⟪ t [ s ] ⟫
  ≡⟨⟩
    ρ ⟪ substOuter s ⟪ t ⟫ˢ ⟫
  ≡⟨ sym (subst-⬖ ρ (substOuter s) t) ⟩
    ρ ⬖ substOuter s ⟪ t ⟫ˢ
  ≡⟨ cong _⟪ t ⟫ˢ (subst-extensionality _ _
      λ { _ Z → refl ; _ (S x) → trans (cong _⟨ x ⟩ˢ (⬖-identʳ ρ)) (subst-outer-abs-suc-renaming ρ (ρ ⟪ s ⟫) x) }) ⟩
    substOuter (ρ ⟪ s ⟫) ⬗ ext ρ ⟪ t ⟫ˢ 
  ≡⟨ subst-⬗ (substOuter (ρ ⟪ s ⟫)) (ext ρ) t ⟩
    substOuter (ρ ⟪ s ⟫) ⟪ ext ρ ⟪ t ⟫ ⟫ˢ
  ≡⟨⟩
    ext ρ ⟪ t ⟫ [ ρ ⟪ s ⟫ ]
  ∎

subst-[] : (t : Γ , τ₁ ⊢ τ₂) (s : Γ ⊢ τ₁) (σ : Subst Γ Δ) → σ ⟪ t [ s ] ⟫ˢ ≡ exts σ ⟪ t ⟫ˢ [ σ ⟪ s ⟫ˢ ]
subst-[] t s σ =
  begin
    σ ⟪ substOuter s ⟪ t ⟫ˢ ⟫ˢ
  ≡⟨ sym (subst-◆ σ (s ∷ idˢ _) t) ⟩
    σ ◆ substOuter s ⟪ t ⟫ˢ
  ≡⟨ subst-ext-var _ _ (λ { τ Z → refl ; τ (S x) → trans (cong _⟨ x ⟩ˢ (◆-identʳ σ)) (subst-outer-abs-suc-subst σ (σ ⟪ s ⟫ˢ) x) }) t ⟩
    substOuter (σ ⟪ s ⟫ˢ) ◆ exts σ ⟪ t ⟫ˢ
  ≡⟨ subst-◆ (substOuter (σ ⟪ s ⟫ˢ)) (exts σ) t ⟩
    substOuter (σ ⟪ s ⟫ˢ) ⟪ exts σ ⟪ t ⟫ˢ ⟫ˢ
  ∎

suc-subst-≡ : (σ₁ σ₂ : Subst Γ Δ) (x : Γ ∋ τ) → σ₁ ⟨ x ⟩ˢ ≡ σ₂ ⟨ x ⟩ˢ → suc-subst {τ = τ₁} σ₁ ⟨ x ⟩ˢ ≡ suc-subst σ₂ ⟨ x ⟩ˢ
suc-subst-≡ σ₁ σ₂ x p =
  begin
    suc-subst σ₁ ⟨ x ⟩ˢ
  ≡⟨ suc-subst-⟨-⟩ˢ σ₁ x ⟩
    suc-renaming (idᴿ _) ⟪ σ₁ ⟨ x ⟩ˢ ⟫
  ≡⟨ cong (suc-renaming (idᴿ _) ⟪_⟫) p ⟩
    suc-renaming (idᴿ _) ⟪ σ₂ ⟨ x ⟩ˢ ⟫
  ≡⟨ sym (suc-subst-⟨-⟩ˢ σ₂ x) ⟩
    suc-subst σ₂ ⟨ x ⟩ˢ
  ∎
