{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂; cong-app; sym; trans; subst)
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to _,ˣ_)

open import Function using (case_of_)

open import Term
open import Renaming
open import Substitution
open import Reduction

module STLC where

module SN where
  -- Strongly normalizing terms, i.e., those terms from which all reduction chains are finite
  data SN : Γ ⊢ τ → Set where
    sn : {t : Γ ⊢ τ} → (∀ s → t ▷ s → SN s) → SN t

  var-is-SN : (x : Γ ∋ τ) → SN (var x)
  var-is-SN x = sn λ _ ()

  SN-closed-▷ :  {t u : Γ ⊢ τ} → t ▷ u → SN t → SN u
  SN-closed-▷ t▷u (sn t∈SN) = t∈SN _ t▷u

  -- we can use simulation arguments to conclude that terms are elements of SN
  -- that is, if a larger term is already strongly normalizing, then its subterms
  -- are also SN because all their reductions apply to the larger term.
  tu∈SN⇒t∈SN : (t : Γ ⊢ τ₁ ⇒ τ₂) (u : Γ ⊢ τ₁) → SN (t ∙ u) → SN t
  tu∈SN⇒t∈SN t u (sn p) = sn λ s t▷s → tu∈SN⇒t∈SN s u (p (s ∙ u) (ξ₁ t▷s))

  t∈SN⇒ƛt∈SN : (t : Γ , τ₁ ⊢ τ₂) → SN t → SN (abs t)
  t∈SN⇒ƛt∈SN t (sn x) = sn λ where (abs s) (ζ t↝s) → t∈SN⇒ƛt∈SN s (x s t↝s)

  SN-renaming : (ρ : Renaming Γ Δ) → (t : Γ ⊢ τ) → SN (ρ ⟪ t ⟫) → SN t
  SN-renaming ρ t (sn tρ∈SN) = sn λ s t▷s → SN-renaming ρ s (tρ∈SN (ρ ⟪ s ⟫) (rename-▷ ρ t▷s))
 
  renaming-SN : (ρ : Renaming Γ Δ) → (t : Γ ⊢ τ) → SN t → SN (ρ ⟪ t ⟫)
  renaming-SN ρ t (sn t∈SN) = sn λ s ρt▷s → case ▷-rename t s ρ ρt▷s of λ where
    (u ,ˣ t▷u ,ˣ ρu≡s) → subst SN ρu≡s (renaming-SN ρ u (t∈SN u t▷u))

  -- multi step strong normalization, sometimes needed for Agda to see termination
  data SN⁺ : Γ ⊢ τ → Set where
    sn : {t : Γ ⊢ τ} → (∀ s → t ▷⁺ s → SN⁺ s) → SN⁺ t

  SN⁺⊆SN : {t : Γ ⊢ τ} → SN⁺ t → SN t
  SN⁺⊆SN (sn t∈SN⁺) = sn λ s t▷s → SN⁺⊆SN (t∈SN⁺ s (t▷s ▷⁺end))

  SN⊆SN⁺ : {t : Γ ⊢ τ} → SN t → SN⁺ t
  SN⊆SN⁺ (sn t∈SN) = sn λ where
    s (t▷s ▷⁺end)       → SN⊆SN⁺ (t∈SN s t▷s)
    s (t▷r ▷⁺step r▷⁺s) → case SN⊆SN⁺ (t∈SN _ t▷r) of λ where (sn r∈SN⁺) → r∈SN⁺ s r▷⁺s

  -- -- Agda does not recognize this version as terminating. Splitting it into two functions works without using wf or similar approach.
  -- SN-closed-β-expansion : (t : Γ , τ₁ ⊢ τ₂) (u : Γ ⊢ τ₁) → SN⁺ (t [ u ]) → SN u → SN (abs t ∙ u)
  -- SN-closed-β-expansion {τ₁ = τ₁} t u (sn t[u]∈SN⁺) (sn u∈SN) = sn λ where
  --   .(t [ u ])   β          → SN⁺⊆SN (sn t[u]∈SN⁺)
  --   .(abs _ ∙ u) (ξ₁ (ζ r)) → SN-closed-β-expansion _ u (t[u]∈SN⁺ _ ((subst-▷ (substOuter u) r) ▷⁺end)) (sn u∈SN)
  --   (abs s ∙ u′) (ξ₂ u▷u′)   → case σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t {σ₁ = substOuter u} {σ₂ = substOuter u′} s (t▷⋆t′⇒[t]▶⋆[t′] (inj₂ (u▷u′ ▷⁺end))) of λ where
  --     (inj₁ t[u]≡t[u′])  → SN-closed-β-expansion t u′ (subst SN⁺ t[u]≡t[u′] (sn t[u]∈SN⁺)) (u∈SN u′ u▷u′)
  --     (inj₂ t[u]▷⁺t[u′]) → SN-closed-β-expansion t u′ (t[u]∈SN⁺ _ t[u]▷⁺t[u′]) (u∈SN u′ u▷u′)

  SN-closed-β-expansion    : (t : Γ , τ₁ ⊢ τ₂) (u : Γ ⊢ τ₁) → SN⁺ (t [ u ]) → SN u → SN (abs t ∙ u)
  SN-closed-β-expansion-sn : (t : Γ , τ₁ ⊢ τ₂) (u : Γ ⊢ τ₁) → SN⁺ (t [ u ]) → SN u → (s : Γ ⊢ τ₂) → abs t ∙ u ▷ s → SN s

  SN-closed-β-expansion    t u t[u]∈SN⁺      u∈SN      = sn (SN-closed-β-expansion-sn t u t[u]∈SN⁺ u∈SN)
  SN-closed-β-expansion-sn t u (sn t[u]∈SN⁺) u∈SN      .(abs _ ∙ u) (ξ₁ (ζ t▷t′)) = SN-closed-β-expansion _ u (t[u]∈SN⁺ _ (((subst-▷ (substOuter u) t▷t′) ▷⁺end))) u∈SN
  SN-closed-β-expansion-sn t u t[u]∈SN⁺      u∈SN      .(t [ u ])   β            = SN⁺⊆SN t[u]∈SN⁺
  SN-closed-β-expansion-sn t u (sn t[u]∈SN⁺) (sn u∈SN) (abs s ∙ u′) (ξ₂ u▷u′)
    with σ₁▶⋆σ₂⇒σ₁t▷⋆σ₂t {σ₁ = substOuter u} {σ₂ = substOuter u′} s (t▷⋆t′⇒[t]▶⋆[t′] (inj₂ (u▷u′ ▷⁺end)))
  ... | inj₁ t[u]≡t[u′]  = SN-closed-β-expansion t u′ (subst SN⁺ t[u]≡t[u′] (sn t[u]∈SN⁺)) (u∈SN u′ u▷u′)
  ... | inj₂ t[u]▷⁺t[u′] = SN-closed-β-expansion t u′ (t[u]∈SN⁺ _ t[u]▷⁺t[u′]) (u∈SN u′ u▷u′)
open SN

module Neutral where
  -- neutral terms: when applied, these terms do not create new redexes
  data NE : Γ ⊢ τ → Set where
    var : (x : Γ ∋ τ) → NE (var x)
    _∙_ : {t : Γ ⊢ τ₁ ⇒ τ₂} → NE t → {u : Γ ⊢ τ₁} → SN u → NE (t ∙ u)

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
