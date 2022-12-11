{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂; cong-app; sym; trans; subst; subst₂)
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to _,ˣ_)

open import Function using (_∘_)

open import Term
open import Renaming
open import Substitution
open import Reduction.Base

module Reduction.Properties where

rename-▷ : (ρ : Renaming Δ Γ) {t s : Δ ⊢ τ} → t ▷ s → ρ ⟪ t ⟫ ▷ ρ ⟪ s ⟫
rename-▷ ρ (ξ₁ r) = ξ₁ (rename-▷ ρ r)
rename-▷ ρ (ξ₂ r) = ξ₂ (rename-▷ ρ r)
rename-▷ ρ (ζ r)  = ζ (rename-▷ (ext ρ) r)
rename-▷ ρ {abs t ∙ s} {r} β = subst (ρ ⟪ abs t ∙ s ⟫ ▷_) (sym (rename-[] t s ρ)) β

▷-rename : (t : Γ ⊢ τ) (u : Δ ⊢ τ) (ρ : Renaming Γ Δ) → ρ ⟪ t ⟫ ▷ u → Σ[ u′ ∈ Γ ⊢ τ ] (t ▷ u′ × ρ ⟪ u′ ⟫ ≡ u)
▷-rename (abs s ∙ t) .(ext ρ ⟪ s ⟫ [ ρ ⟪ t ⟫ ]) ρ β = s [ t ] ,ˣ β ,ˣ rename-[] s t ρ
▷-rename (s ∙ t) .(_ ∙ ρ ⟪ t ⟫) ρ (ξ₁ r) with ▷-rename s _ ρ r
... | u′ ,ˣ s▷u′ ,ˣ ρu′≡s′ = u′ ∙ t ,ˣ ξ₁ s▷u′ ,ˣ cong (_∙ _) ρu′≡s′
▷-rename (s ∙ t) .(ρ ⟪ s ⟫ ∙ _) ρ (ξ₂ r) with ▷-rename t _ ρ r
... | u′ ,ˣ t▷u′ ,ˣ ρu′≡t′ = s ∙ u′ ,ˣ ξ₂ t▷u′ ,ˣ cong (_ ∙_) ρu′≡t′
▷-rename (abs t) (abs u) ρ (ζ t↝u) with ▷-rename t u (ext ρ) t↝u
... | u′ ,ˣ t▷u′ ,ˣ ρu′≡u = abs u′ ,ˣ ζ t▷u′ ,ˣ cong abs ρu′≡u

suc-subst-▷ : (σ : Subst Γ Δ) {s t : Γ ⊢ τ} → σ ⟪ t ⟫ˢ ▷ σ ⟪ s ⟫ˢ → suc-subst {τ = τ₁} σ ⟪ t ⟫ˢ ▷ suc-subst σ ⟪ s ⟫ˢ
suc-subst-▷ σ {s = s} {t = t} σt▷σs = subst₂ _▷_ (sym (suc-subst-⟪-⟫ˢ σ t)) (sym (suc-subst-⟪-⟫ˢ σ s)) (rename-▷ (suc-renaming (idᴿ _)) σt▷σs)

subst-▷ : (σ : Subst Δ Γ) {t s : Δ ⊢ τ} → t ▷ s → σ ⟪ t ⟫ˢ ▷ σ ⟪ s ⟫ˢ
subst-▷ σ (ξ₁ t▷s) = ξ₁ (subst-▷ σ t▷s)
subst-▷ σ (ξ₂ t▷s) = ξ₂ (subst-▷ σ t▷s)
subst-▷ σ (ζ t▷s)  = ζ (subst-▷ (exts σ) t▷s)
subst-▷ σ {t = abs s ∙ t} β = subst (σ ⟪ abs s ∙ t ⟫ˢ ▷_) (sym (subst-[] s t σ)) β


--------------------------------------------------------------------------------
---- Transitive Closure                                                     ----
--------------------------------------------------------------------------------

rename-▷⁺ : (ρ : Renaming Δ Γ) {t s : Δ ⊢ τ} → t ▷⁺ s → ρ ⟪ t ⟫ ▷⁺ ρ ⟪ s ⟫
rename-▷⁺ ρ (r ▷⁺end)    = rename-▷ ρ r ▷⁺end
rename-▷⁺ ρ (r ▷⁺step s) = rename-▷ ρ r ▷⁺step rename-▷⁺ ρ s

subst-▷⁺ : (σ : Subst Δ Γ) {t s : Δ ⊢ τ} → t ▷⁺ s → σ ⟪ t ⟫ˢ ▷⁺ σ ⟪ s ⟫ˢ
subst-▷⁺ σ (r ▷⁺end)    = subst-▷ σ r ▷⁺end
subst-▷⁺ σ (r ▷⁺step s) = subst-▷ σ r ▷⁺step subst-▷⁺ σ s

▷⁺-trans : {r s t : Γ ⊢ τ} → r ▷⁺ s → s ▷⁺ t → r ▷⁺ t
▷⁺-trans (r▷s ▷⁺end)       s▷⁺t = r▷s ▷⁺step s▷⁺t
▷⁺-trans (r▷u ▷⁺step u▷⁺s) s▷⁺t = r▷u ▷⁺step ▷⁺-trans u▷⁺s s▷⁺t

ξ₁⁺ : {s t : Γ ⊢ τ₁ ⇒ τ₂} {r : Γ ⊢ τ₁} → s ▷⁺ t → s ∙ r ▷⁺ t ∙ r
ξ₁⁺ (s▷t ▷⁺end)       = ξ₁ s▷t ▷⁺end
ξ₁⁺ (s▷u ▷⁺step u▷⁺t) = ξ₁ s▷u ▷⁺step ξ₁⁺ u▷⁺t

ξ₂⁺ : {r : Γ ⊢ τ₁ ⇒ τ₂} {s t : Γ ⊢ τ₁} → s ▷⁺ t → r ∙ s ▷⁺ r ∙ t
ξ₂⁺ (s▷t ▷⁺end)       = ξ₂ s▷t ▷⁺end
ξ₂⁺ (s▷u ▷⁺step u▷⁺t) = ξ₂ s▷u ▷⁺step ξ₂⁺ u▷⁺t

ζ⁺ : {s t : Γ , τ₁ ⊢ τ₂} → s ▷⁺ t → abs s ▷⁺ abs t
ζ⁺ (s▷t ▷⁺end)       = ζ s▷t ▷⁺end
ζ⁺ (s▷u ▷⁺step u▷⁺t) = ζ s▷u ▷⁺step ζ⁺ u▷⁺t


--------------------------------------------------------------------------------
---- Reflexive Transitive Closure                                           ----
--------------------------------------------------------------------------------

rename-▷⋆ : (ρ : Renaming Δ Γ) {t s : Δ ⊢ τ} → t ▷⋆ s → ρ ⟪ t ⟫ ▷⋆ ρ ⟪ s ⟫
rename-▷⋆ ρ (inj₁ refl) = inj₁ refl
rename-▷⋆ ρ (inj₂ t▷⁺s) = inj₂ (rename-▷⁺ ρ t▷⁺s)

▷⋆-trans : {r s t : Γ ⊢ τ} → r ▷⋆ s → s ▷⋆ t → r ▷⋆ t
▷⋆-trans (inj₁ refl) s▷⋆t        = s▷⋆t
▷⋆-trans r▷⋆s        (inj₁ refl) = r▷⋆s
▷⋆-trans (inj₂ r▷⁺s) (inj₂ s▷⁺t) = inj₂ (▷⁺-trans r▷⁺s s▷⁺t)

ξ₁⋆ : {s t : Γ ⊢ τ₁ ⇒ τ₂} {r : Γ ⊢ τ₁} → s ▷⋆ t → s ∙ r ▷⋆ t ∙ r
ξ₁⋆ (inj₁ refl) = inj₁ refl
ξ₁⋆ (inj₂ s▷⁺t) = inj₂ (ξ₁⁺ s▷⁺t)

ξ₂⋆ : {r : Γ ⊢ τ₁ ⇒ τ₂} {s t : Γ ⊢ τ₁} → s ▷⋆ t → r ∙ s ▷⋆ r ∙ t
ξ₂⋆ (inj₁ refl) = inj₁ refl
ξ₂⋆ (inj₂ s▷⁺t) = inj₂ (ξ₂⁺ s▷⁺t)

ζ⋆ : {s t : Γ , τ₁ ⊢ τ₂} → s ▷⋆ t → abs s ▷⋆ abs t
ζ⋆ (inj₁ refl) = inj₁ refl
ζ⋆ (inj₂ s▷⁺t) = inj₂ (ζ⁺ s▷⁺t)


--------------------------------------------------------------------------------
---- Substitution and Reduction interaction                                 ----
--------------------------------------------------------------------------------

exts-▶⋆ : (σ₁ σ₂ : Subst Γ Δ) → σ₁ ▶⋆ σ₂ → exts {τ = τ} σ₁ ▶⋆ exts σ₂
exts-▶⋆ σ₁ σ₂ p Z = inj₁ refl
exts-▶⋆ σ₁ σ₂ p (S x) with p x
... | inj₁ p = inj₁ (suc-subst-≡ σ₁ σ₂ x p)
... | inj₂ r = inj₂ (subst₂ _▷⁺_ (sym (suc-subst-⟨-⟩ˢ σ₁ x)) (sym (suc-subst-⟨-⟩ˢ σ₂ x)) (rename-▷⁺ (suc-renaming (idᴿ _)) r))

t▷⋆t′⇒[t]▶⋆[t′] : {t u : Γ ⊢ τ} → t ▷⋆ u → substOuter t ▶⋆ substOuter u
t▷⋆t′⇒[t]▶⋆[t′] (inj₁ refl) x     = inj₁ refl
t▷⋆t′⇒[t]▶⋆[t′] (inj₂ t▷⁺u) Z     = inj₂ t▷⁺u
t▷⋆t′⇒[t]▶⋆[t′] (inj₂ t▷⁺u) (S x) = inj₁ refl

σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t : {σ₁ σ₂ : Subst Γ Δ} (t : Γ ⊢ τ) → σ₁ ▶⋆ σ₂ → σ₁ ⟪ t ⟫ˢ ▷⋆ σ₂ ⟪ t ⟫ˢ
σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t (var x) p = p x
σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t (s ∙ t) p = ▷⋆-trans (ξ₁⋆ (σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t s p)) (ξ₂⋆ (σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t t p))
σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t (abs t) p = ζ⋆ (σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t t (exts-▶⋆ _ _ p))


--------------------------------------------------------------------------------
---- Weak Head Reduction                                                    ----
--------------------------------------------------------------------------------

rename-▷ʷ : (ρ : Renaming Δ Γ) {t s : Δ ⊢ τ} → t ▷ʷ s → ρ ⟪ t ⟫ ▷ʷ ρ ⟪ s ⟫
rename-▷ʷ ρ (ξ₁ t▷ʷs) = ξ₁ (rename-▷ʷ ρ t▷ʷs)
rename-▷ʷ ρ {abs t ∙ s} β = subst (ρ ⟪ abs t ∙ s ⟫ ▷ʷ_) (sym (rename-[] t s ρ)) β

▷ʷ-▷-pseudo-locally-confluent : (t t′ t″ : Γ ⊢ τ) → t ▷ʷ t′ → t ▷ t″ → t′ ≡ t″ ⊎ Σ[ w ∈ Γ ⊢ τ ] (t″ ▷ʷ w × t′ ▷⋆ w)
▷ʷ-▷-pseudo-locally-confluent .(_ ∙ _)     .(_ ∙ _)   .(_ ∙ _) (ξ₁ r) (ξ₁ s) with ▷ʷ-▷-pseudo-locally-confluent _ _ _ r s
... | inj₁ refl = inj₁ refl
... | inj₂ (w ,ˣ r ,ˣ s) = inj₂ (w ∙ _ ,ˣ ξ₁ r ,ˣ ξ₁⋆ s)
▷ʷ-▷-pseudo-locally-confluent .(_ ∙ _) .(_ ∙ _) .(_ ∙ _) (ξ₁ r) (ξ₂ s) = inj₂ (_ ∙ _ ,ˣ ξ₁ r ,ˣ inj₂ (ξ₂ s ▷⁺end))
▷ʷ-▷-pseudo-locally-confluent .(abs t₁ ∙ t₂) .(t₁ [ t₂ ]) .(t₁ [ t₂ ])  (β {s = t₁} {t = t₂}) β          = inj₁ refl

▷ʷ-▷-pseudo-locally-confluent .(abs t₁ ∙ t₂) .(t₁ [ t₂ ]) .(abs _ ∙ t₂) (β {s = t₁} {t = t₂}) (ξ₁ (ζ s)) = inj₂ (conf-β-ξ₁ t₁ _ t₂ s)
  where
    conf-β-ξ₁ : (t₁ t₁′ : Γ , τ ⊢ τ₂) (t₂ : Γ ⊢ τ) → t₁ ▷ t₁′ → Σ[ w ∈ Γ ⊢ τ₂ ] (abs t₁′ ∙ t₂ ▷ʷ w × t₁ [ t₂ ] ▷⋆ w)
    conf-β-ξ₁ t₁ t₁′ t₂ x = t₁′ [ t₂ ] ,ˣ β ,ˣ inj₂ (subst-▷⁺ (substOuter t₂) (x ▷⁺end))

▷ʷ-▷-pseudo-locally-confluent .(abs t₁ ∙ t₂) .(t₁ [ t₂ ]) .(abs t₁ ∙ _) (β {s = t₁} {t = t₂}) (ξ₂ s)     = inj₂ (conf-β-ξ₂ t₁ t₂ _ s)
  where
    conf-β-ξ₂ : (t₁ : Γ , τ ⊢ τ₂) (t₂ t₂′ : Γ ⊢ τ) → t₂ ▷ t₂′ → Σ[ w ∈ Γ ⊢ τ₂ ] (abs t₁ ∙ t₂′ ▷ʷ w × t₁ [ t₂ ] ▷⋆ w)
    conf-β-ξ₂ t₁ t₂ t₂′ x = t₁ [ t₂′ ] ,ˣ β ,ˣ σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t t₁ (t▷⋆t′⇒[t]▶⋆[t′] (inj₂ (x ▷⁺end)))
