{-# OPTIONS --without-K #-}

open import Data.Unit hiding (_≟_)
open import Data.Empty
open import Data.Nat hiding (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _×_) renaming (_,_ to ⟨_,_⟩)

open import Induction.WellFounded

open import Function using (id; _∘_; case_return_of_; case_of_; _|>_)
open import Relation.Nullary using (Dec; _because_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; cong₂; cong-app; sym) renaming (subst to subst-≡)
open        Relation.Binary.PropositionalEquality.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Axiom.Extensionality.Propositional

module Sketch where

postulate
  funExt : ∀ {a b} → Extensionality a b
  impFunExt : ∀ {a b} → ExtensionalityImplicit a b

module Defs where
  infixl 5 _,_
  infix  4 _∋_
  infix  4 _⊢_
  infixr 7 _⇒_
  infixl 7 _∙_
  
  data Type : Set where
    ⋆   : Type
    _⇒_ : Type → Type → Type
  
  variable σ τ : Type
  
  data Ctx : Set where
    ∅   : Ctx
    _,_ : Ctx → Type → Ctx
  
  variable Γ Δ Ω : Ctx
  
  _ : Ctx
  _  = ∅ , ⋆ , (⋆ ⇒ ⋆) -- a context containing a variable of type ⋆ and a variable of type ⋆ ⇒ ⋆
  
  -- Proof that a variable of a type is in a Context/the deBrujin index
  data _∋_ : Ctx → Type → Set where
    Z : Γ , σ ∋ σ
    S_ : Γ ∋ σ → Γ , τ ∋ σ
  
  -- Intrinsically-typed terms
  data _⊢_ : Ctx → Type → Set where
    var : Γ ∋ τ
        → Γ ⊢ τ
    _∙_ : Γ ⊢ σ ⇒ τ
        → Γ ⊢ σ
        → Γ ⊢ τ
    abs : Γ , σ ⊢ τ
        → Γ ⊢ σ ⇒ τ

  Renaming : (Γ Δ : Ctx) → Set
  Renaming Γ Δ = {σ : Type} → Γ ∋ σ → Δ ∋ σ

  idᴿ : (Γ : Ctx) → Renaming Γ Γ
  idᴿ _ = id

  Subst : (Γ Δ : Ctx) → Set
  Subst Γ Δ = {σ : Type} → Γ ∋ σ → Δ ⊢ σ

  idˢ : Subst Γ Γ
  idˢ = var
  
  -- extend renaming by variable
  ext : Renaming Γ Δ → Renaming (Γ , σ) (Δ , σ)
  ext ρ Z     = Z
  ext ρ (S x) = S (ρ x)

  exte : Renaming Γ Δ → (σ : Type) → Renaming (Γ , σ) (Δ , σ)
  exte ρ σ = ext {σ = σ} ρ
  
  -- lift renaming to terms
  rename : (∀ {τ} → Γ ∋ τ → Δ ∋ τ)
         → (∀ {τ} → Γ ⊢ τ → Δ ⊢ τ)
  rename ρ (var x) = var (ρ x)
  rename ρ (s ∙ t) = rename ρ s ∙ rename ρ t
  rename ρ (abs t) = abs (rename (ext ρ) t)
  
  -- extend a substitution (similar to ext but we allow terms not only vars)
  exts : Subst Γ Δ → Subst (Γ , σ) (Δ , σ)
  exts σ Z     = var Z
  exts σ (S x) = rename S_ (σ x)

  extse : Subst Γ Δ → (σ : Type) → Subst (Γ , σ) (Δ , σ)
  extse σ τ = exts {σ = τ} σ
  
  -- now we can lift a mapping from vars to terms to a map between terms
  subst : (∀ {τ}   → Γ ∋ τ     → Δ ⊢ τ)
        → (∀ {τ}   → Γ ⊢ τ     → Δ ⊢ τ)
  subst σ (var x) = σ x
  subst σ (s ∙ t) = subst σ s ∙ subst σ t
  subst σ (abs t) = abs (subst (exts σ) t)
  
  substLast : (s : Γ ⊢ τ) → Subst (Γ , τ) Γ
  substLast s Z     = s  
  substLast _ (S i) = var i

  _[_] : Γ , σ ⊢ τ → Γ ⊢ σ → Γ ⊢ τ
  t [ s ] = subst (substLast s) t -- replace outer most free vars with given s and decrease all others because we loose a free var
  
  -- Some properties for later
  renamingExt : (ρ σ : Renaming Γ Δ) → ({τ : Type} (x : Γ ∋ τ) → ρ x ≡ σ x) → _≡_ {A = Renaming Γ Δ} ρ σ
  renamingExt ρ σ p = impFunExt λ {τ} → funExt (λ x → p x)

  ext-id : ∀ Γ σ → _≡_ {A = Renaming (Γ , σ) (Γ , σ)} (exte (idᴿ Γ) σ) (idᴿ (Γ , σ))
  ext-id Γ σ = renamingExt (exte (idᴿ Γ) σ) (idᴿ (Γ , σ)) λ { Z → refl ; (S x) → refl }

  rename-id : (t : Γ ⊢ τ) → rename id t ≡ t
  rename-id (var x) = refl
  rename-id (s ∙ t) = cong₂ _∙_ (rename-id s) (rename-id t)
  rename-id {Γ} {τ = σ ⇒ _} (abs {σ = τ} t) = cong abs
    (begin rename (ext (idᴿ Γ)) t ≡⟨ cong {A = Renaming _ _} (λ - → rename - t) (ext-id Γ σ) ⟩ rename (idᴿ (Γ , _)) t ≡⟨ rename-id t ⟩ t ∎)

  ext-∘ : ∀ σ (γ : Renaming Γ Δ) (ρ : Renaming Ω Γ) → _≡_ {A = Renaming (Ω , σ) (Δ , σ)} (exte (γ ∘ ρ) σ) (exte γ σ ∘ exte ρ σ)
  ext-∘ σ γ ρ = renamingExt _ _ λ { Z → refl ; (S x) → refl }

  rename-∘ : (γ : Renaming Δ Ω) (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → rename (γ ∘ ρ) t ≡ rename γ (rename ρ t)
  rename-∘ γ ρ (var x) = refl
  rename-∘ γ ρ (s ∙ t) = cong₂ _∙_ (rename-∘ γ ρ s) (rename-∘ γ ρ t)
  rename-∘ γ ρ (abs t) = cong abs
    (begin
      rename (ext (γ ∘ ρ)) t
    ≡⟨ cong {A = Renaming _ _} (λ - → rename - t) (ext-∘ _ γ ρ) ⟩
      rename (ext γ ∘ ext ρ) t
    ≡⟨ rename-∘ (ext γ) (ext ρ) t ⟩
      rename (ext γ) (rename (ext ρ) t)
    ∎)

  substExt : (ρ σ : Subst Γ Δ) → ({τ : Type} (x : Γ ∋ τ) → ρ x ≡ σ x) → _≡_ {A = Subst Γ Δ} ρ σ
  substExt ρ σ p = impFunExt λ {τ} → funExt (λ x → p x)

  exts-id : ∀ {τ} → _≡_ {A = Subst (Γ , τ) (Γ , τ)} (extse idˢ τ) idˢ
  exts-id = substExt _ _ λ { Z → refl ; (S x) → refl }

  subst-id : (t : Γ ⊢ τ) → subst var t ≡ t
  subst-id (var x) = refl
  subst-id (s ∙ t) = cong₂ _∙_ (subst-id s) (subst-id t)
  subst-id (abs t) = cong abs (begin subst (exts var) t ≡⟨ cong {A = Subst _ _} (λ - → subst - t) exts-id ⟩ subst var t ≡⟨ subst-id t ⟩ t ∎)

  _◇_ : (ρ : Subst Γ Δ) (σ : Subst Ω Γ) → Subst Ω Δ
  (ρ ◇ σ) t = subst ρ (σ t)

  rename-weaken : (ρ : Renaming Δ Ω) (t : Δ ⊢ τ) → rename (exte ρ σ) (rename S_ t) ≡ rename S_ (rename ρ t)
  rename-weaken ρ t =
    begin
      rename (ext ρ) (rename S_ t)
    ≡⟨ sym (rename-∘ _ _ t) ⟩
      rename (ext ρ ∘ S_) t
    ≡⟨ refl ⟩
      rename (S_ ∘ ρ) t
    ≡⟨ rename-∘ _ _ t ⟩
      rename S_ (rename ρ t)
    ∎

  rename-subst : (ρ : Renaming Γ Δ) (σ : Subst Ω Γ) (t : Ω ⊢ τ) → rename ρ (subst σ t) ≡ subst (λ x → rename ρ (σ x)) t
  rename-subst ρ σ (var x) = refl
  rename-subst ρ σ (s ∙ t) = cong₂ _∙_ (rename-subst ρ σ s) (rename-subst ρ σ t)
  rename-subst ρ σ (abs t) = cong abs
    (begin
      rename (ext ρ) (subst (exts σ) t)
    ≡⟨ rename-subst (ext ρ) (exts σ) t ⟩
      subst (λ z → rename (ext ρ) (exts σ z)) t
    ≡⟨ cong {A = Subst _ _} (λ - → subst - t) (substExt _ _ λ { Z → refl ; (S x) → rename-weaken ρ (σ x) }) ⟩
      subst (exts (λ z → rename ρ (σ z))) t
    ∎)

  subst-rename : (σ : Subst Γ Δ) (ρ : Renaming Ω Γ) (t : Ω ⊢ τ) → subst (λ z → σ (ρ z)) t ≡ subst σ (rename ρ t)
  subst-rename σ ρ (var x) = refl
  subst-rename σ ρ (s ∙ t) = cong₂ _∙_ (subst-rename σ ρ s) (subst-rename σ ρ t)
  subst-rename σ ρ (abs t) = cong abs
    (begin
      subst (exts (λ z → σ (ρ z))) t
    ≡⟨ cong {A = Subst _ _} (λ - → subst - t) (substExt _ _ λ { Z → refl ; (S x) → refl }) ⟩
      subst (λ z → exts σ (ext ρ z)) t
    ≡⟨ subst-rename (exts σ) (ext ρ) t ⟩
      subst (exts σ) (rename (ext ρ) t)
    ∎)

  exts-◇' : ∀ τ α → (ρ : Subst Γ Δ) (σ : Subst Ω Γ) (x : Ω , τ ∋ α) → (extse (ρ ◇ σ) τ) x ≡ (extse ρ τ ◇ extse σ τ) x
  exts-◇' τ .τ ρ σ Z     = refl
  exts-◇' τ α  ρ σ (S x) =
    begin
      extse (ρ ◇ σ) τ (S x)
    ≡⟨ refl ⟩
      rename S_ (subst ρ (σ x))
    ≡⟨ rename-subst S_ ρ (σ x) ⟩
      subst (λ z → rename S_ (ρ z)) (σ x)
    ≡⟨ subst-rename (extse ρ τ) S_ (σ x) ⟩
      subst (extse ρ τ) (rename S_ (σ x))
    ≡⟨ refl ⟩
      subst (extse ρ τ) (extse σ τ (S x))
    ≡⟨ refl ⟩
      (extse ρ τ ◇ extse σ τ) (S x)
    ∎

  exts-◇ : ∀ τ → (ρ : Subst Γ Δ) (σ : Subst Ω Γ) → _≡_ {A = Subst _ _} (extse (ρ ◇ σ) τ) (extse ρ τ ◇ extse σ τ)
  exts-◇ τ ρ σ = substExt _ _ (exts-◇' _ _ ρ σ)

  subst-∘ : (ρ : Subst Γ Δ) (σ : Subst Ω Γ) (t : Ω ⊢ τ) → subst (ρ ◇ σ) t ≡ (subst ρ ∘ subst σ) t
  subst-∘ ρ σ (var x) = refl
  subst-∘ ρ σ (s ∙ t) = cong₂ _∙_ (subst-∘ ρ σ s) (subst-∘ ρ σ t)
  subst-∘ ρ σ (abs t) = cong abs
    (begin
      subst (exts (ρ ◇ σ)) t
    ≡⟨ cong {A = Subst _ _} (λ - → subst - t) (exts-◇ _ ρ σ) ⟩
      subst (exts ρ ◇ exts σ) t
    ≡⟨ subst-∘ (exts ρ) (exts σ) t ⟩
      subst (exts ρ) (subst (exts σ) t)
    ∎)

  rename-∘-[] : (ρ : Renaming Γ Δ) (s : Γ , σ ⊢ τ) (t : Γ ⊢ σ) → _≡_ {A = Δ ⊢ τ} (rename ρ (s [ t ])) ((rename (ext ρ) s) [ (rename ρ t) ])
  rename-∘-[] ρ s t =
    begin
      rename ρ (s [ t ])
    ≡⟨ refl ⟩
      rename ρ (subst _ s)
    ≡⟨ rename-subst ρ _ s ⟩
      subst (λ x → rename ρ _) s
    ≡⟨ cong {A = Subst _ _} (λ - → subst - s) (substExt _ _ λ{ Z → refl ; (S x) → refl }) ⟩
      subst _ s
    ≡⟨ subst-rename _ (ext ρ) s ⟩
      subst _ (rename (ext ρ) s)
    ≡⟨ refl ⟩
      (rename (ext ρ) s) [ (rename ρ t) ]
    ∎

  subst-∘-[] : {τ₁ τ₂ : Type} (t : Γ ⊢ τ₁) (s : Γ , τ₁ ⊢ τ₂) (σ : Subst Γ Δ) → subst (exts σ) s [ subst σ t ] ≡ subst σ (s [ t ])
  subst-∘-[] t s σ =
    begin
      subst (exts σ) s [ subst σ t ]
    ≡⟨ sym (subst-∘ (substLast (subst σ t)) (exts σ) s) ⟩
      subst (substLast (subst σ t) ◇ exts σ) s
    ≡⟨ cong {A = Subst _ _} (λ t → subst t s) (substExt _ _ (λ { Z → refl ; (S i) →
        begin
          subst (substLast (subst σ t)) (exts σ (S i))
        ≡⟨ refl ⟩
          subst (substLast (subst σ t)) (rename S_ (σ i))
        ≡⟨ sym (subst-rename (substLast (subst σ t)) S_ (σ i)) ⟩
          subst (λ x → substLast (subst σ t) (S x)) (σ i)
        ≡⟨ refl ⟩
          subst var (σ i)
        ≡⟨ subst-id (σ i) ⟩
          σ i
        ∎ })) ⟩
      subst (σ ◇ substLast t) s
    ≡⟨ subst-∘ σ (substLast t) s ⟩
      subst σ (s [ t ])
    ∎
open Defs

module Red where
  infix 5 _↝_ _↜_

  -- Reduction relation
  data _↝_ : Γ ⊢ τ → Γ ⊢ τ → Set where
    ξ₁ : {s s' : Γ ⊢ σ ⇒ τ} {t  : Γ ⊢ σ}
       → s ↝ s'
       → s ∙ t ↝ s' ∙ t
  
    ξ₂ : {s : Γ ⊢ σ ⇒ τ} {t t' : Γ ⊢ σ}
       → t ↝ t'
       → s ∙ t ↝ s ∙ t'
  
    β : {s : Γ , σ ⊢ τ} {t : Γ ⊢ σ}
      → abs s ∙ t ↝ s [ t ]
  
    ζ : {s t : Γ , σ ⊢ τ}
      → s ↝ t
      → abs s ↝ abs t

  _↜_ : Γ ⊢ τ → Γ ⊢ τ → Set
  t ↜ s = s ↝ t

  -- Reduction interacts with renamings as one would expect
  ↝-rename : (t : Γ ⊢ τ) (u : Δ ⊢ τ) (ρ : Renaming Γ Δ) → rename ρ t ↝ u → Σ[ u′ ∈ Γ ⊢ τ ] (t ↝ u′ × rename ρ u′ ≡ u)
  ↝-rename (abs s ∙ t) .(rename (ext ρ) s [ rename ρ t ]) ρ β      = ⟨ s [ t ] , ⟨ β , rename-∘-[] ρ s t ⟩ ⟩
  ↝-rename (s ∙ t)     .(_          ∙ rename ρ t)         ρ (ξ₁ r) with ↝-rename s _ ρ r
  ... | ⟨ u' , ⟨ s↝u' , u'ρ≡s' ⟩ ⟩ = ⟨ u' ∙ t , ⟨ ξ₁ s↝u' , cong (_∙ _) u'ρ≡s' ⟩ ⟩
  ↝-rename (s ∙ t)     .(rename ρ s ∙ _)                  ρ (ξ₂ r) with ↝-rename t _ ρ r
  ... | ⟨ u' , ⟨ t↝u' , u'ρ≡t' ⟩ ⟩ = ⟨ s ∙ u' , ⟨ ξ₂ t↝u' , cong (_ ∙_) u'ρ≡t' ⟩ ⟩
  ↝-rename (abs t) (abs u) ρ (ζ t↝u) with ↝-rename t u (ext ρ) t↝u
  ... | ⟨ u' , ⟨ t↝u' , u'ρ≡u ⟩ ⟩ = ⟨ abs u' , ⟨ ζ t↝u' , cong abs u'ρ≡u ⟩ ⟩

  rename-↝ : (t u : Γ ⊢ τ) (ρ : Renaming Γ Δ) → t ↝ u → rename ρ t ↝ rename ρ u
  rename-↝ .(_ ∙ _)     .(_ ∙ _)   ρ (ξ₁ t↝u) = ξ₁ (rename-↝ _ _ ρ t↝u)
  rename-↝ .(_ ∙ _)     .(_ ∙ _)   ρ (ξ₂ t↝u) = ξ₂ (rename-↝ _ _ ρ t↝u)
  rename-↝ .(abs _)     .(abs _)   ρ (ζ t↝u)  = ζ  (rename-↝ _ _ (ext ρ) t↝u)
  rename-↝ (abs t ∙ u) .(t [ u ])  ρ β        = subst-≡ (abs (rename (ext ρ) t) ∙ rename ρ u ↝_) (sym (rename-∘-[] ρ t u)) β

  subst-↝ : {τ₁ τ₂ : Type} (t s : Γ , τ₁ ⊢ τ₂) → t ↝ s → (σ : Subst (Γ , τ₁) Δ) → subst σ t ↝ subst σ s
  subst-↝ (_ ∙ _)     .(_ ∙ _) (ξ₁ x) σ = ξ₁ (subst-↝ _ _ x σ)
  subst-↝ (_ ∙ _)     .(_ ∙ _) (ξ₂ x) σ = ξ₂ (subst-↝ _ _ x σ)
  subst-↝ (abs _)     .(abs _) (ζ x)  σ = ζ  (subst-↝ _ _ x (exts σ))
  subst-↝ (abs s ∙ t) .(_)     β      σ = subst-≡ (subst σ (abs s ∙ t) ↝_) (subst-∘-[] t s σ) β

  -- strongly normalizing terms
  -- the type of terms t such that all reduction sequences are finite
  data SN : Γ ⊢ τ → Set where
    sn : {t : Γ ⊢ τ} → (∀ s → t ↝ s → SN s) → SN t

  t∈SN⇒↝-WF : (t : Γ ⊢ τ) → SN t → Acc _↜_ t
  t∈SN⇒↝-WF t (sn t∈SN) = acc λ s s↜t → t∈SN⇒↝-WF s (t∈SN s s↜t)

  t∈SN⇒↝⋆-WF : (t : Γ ⊢ τ) → SN t → Acc _↜_ t
  t∈SN⇒↝⋆-WF t (sn t∈SN) = acc λ s s↜t → t∈SN⇒↝-WF s (t∈SN s s↜t)

  x∈SN : (x : Γ ∋ τ) → SN (var x)
  x∈SN x = sn λ where _ () -- variables do not reduce, thus all reducts are SN

  -- SN-trans : (t u : Γ ⊢ τ) → SN t → t ↝⋆ u → SN u
  -- SN-trans t .t t∈SN ↝refl = t∈SN
  -- SN-trans t u (sn t∈SN) (↝trans t↝r r↝⋆u) = SN-trans _ u (t∈SN _ t↝r) r↝⋆u

  -- we can use simulation arguments to conclude that terms are elements of SN
  -- that is, if a larger term is already strongly normalizing, then its subterms
  -- are also SN because all their reductions apply to the larger term.
  tu∈SN⇒t∈SN : (t : Γ ⊢ σ ⇒ τ) (u : Γ ⊢ σ) → SN (t ∙ u) → SN t
  tu∈SN⇒t∈SN t u (sn tu∈SN) = sn λ s t↝s → tu∈SN⇒t∈SN s u (tu∈SN (s ∙ u) (ξ₁ t↝s))

  -- closure properties of SN

  SN-closed-renaming : (Γ : Ctx) (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → SN (rename ρ t) → SN t
  SN-closed-renaming Γ ρ t (sn tρ∈SN) = sn λ s t↝s → SN-closed-renaming Γ ρ s (tρ∈SN (rename ρ s) (rename-↝ t s ρ t↝s))

  SN-closed-renaming← : (Γ : Ctx) (ρ : Renaming Γ Δ) (t : Γ ⊢ τ) → SN t → SN (rename ρ t)
  SN-closed-renaming← Γ ρ t (sn t∈SN) = sn λ s t↝s →
    let ⟨ s′ , ⟨ t↝s′ , renaming-s′≡s ⟩ ⟩ =  ↝-rename t s ρ t↝s
    in subst-≡ SN renaming-s′≡s (SN-closed-renaming← Γ ρ s′ (t∈SN s′ t↝s′))

  SN-closed-abs : (t : Γ , σ ⊢ τ) → SN t → SN (abs t)
  SN-closed-abs t (sn t∈SN) = sn λ where (abs u) (ζ t↝u) → SN-closed-abs u (t∈SN u t↝u)
  
  SN-closed-forwards-red : (t s : Γ ⊢ τ) → SN t → (t ↝ s) → SN s
  SN-closed-forwards-red t s (sn t∈SN) t↝s = t∈SN s t↝s
open Red

-- transitive closure of reduction relation
infix 5 _↝⁺_
data _↝⁺_ : Γ ⊢ τ → Γ ⊢ τ → Set where
  ↝lift  : {s t : Γ ⊢ τ} → s ↝ t → s ↝⁺ t
  ↝trans : {s t r : Γ ⊢ τ}
         → s ↝  t
         → t ↝⁺ r
         → s ↝⁺ r

infix 5 _↝⋆_
_↝⋆_ : Γ ⊢ τ → Γ ⊢ τ → Set
s ↝⋆ t = s ≡ t ⊎ s ↝⁺ t

data SN⁺ : Γ ⊢ τ → Set where
  sn : {t : Γ ⊢ τ} → (∀ s → t ↝⁺ s → SN⁺ s) → SN⁺ t

rename-↝⁺ : (ρ : Renaming Γ Δ) (s t : Γ ⊢ τ) → s ↝⁺ t → rename ρ s ↝⁺ rename ρ t
rename-↝⁺ ρ s t (↝lift s↝t) = ↝lift (rename-↝ s t ρ s↝t)
rename-↝⁺ ρ s t (↝trans s↝r r↝⁺t) = ↝trans (rename-↝ s _ ρ s↝r) (rename-↝⁺ ρ _ t r↝⁺t)

SN⊆SN⁺ : (t : Γ ⊢ τ) → SN t → SN⁺ t
SN⊆SN⁺ t (sn t∈SN) = sn λ where
  s (↝lift t↝s)      → SN⊆SN⁺ s (t∈SN s t↝s)
  s (↝trans t↝r r↝s) → case SN⊆SN⁺ _ (t∈SN _ t↝r) of λ where (sn p) → p s r↝s

SN⁺⊆SN : (t : Γ ⊢ τ) → SN⁺ t → SN t
SN⁺⊆SN t (sn t∈SN⁺) = sn λ where
  s t↝s → SN⁺⊆SN s (t∈SN⁺ s (↝lift t↝s))

subst-red : (σ σ′ : Subst Γ Δ) → Set
subst-red σ σ′ = ∀ {τ} (x : _ ∋ τ) → σ x ≡ σ′ x ⊎ σ x ↝⁺ σ′ x

ext-subst-red : (σ σ′ : Subst Γ Δ) → subst-red σ σ′ → subst-red (extse σ τ) (extse σ′ τ)
ext-subst-red σ σ′ p Z     = inj₁ refl
ext-subst-red σ σ′ p (S x) with p x
... | inj₁ p = inj₁ (cong (rename S_) p)
... | inj₂ q = inj₂ (rename-↝⁺ S_ (σ x) (σ′ x) q)

ζ⁺ : (s t : Γ , σ ⊢ τ) → s ↝⁺ t → abs s ↝⁺ abs t
ζ⁺ s t (↝lift s↝t) = ↝lift (ζ s↝t)
ζ⁺ s t (↝trans s↝r r↝⁺t) = ↝trans (ζ s↝r) (ζ⁺ _ t r↝⁺t)

ζ⋆ : (s t : Γ , σ ⊢ τ) → s ↝⋆ t → abs s ↝⋆ abs t
ζ⋆ s t (inj₁ p) = inj₁ (cong abs p)
ζ⋆ s t (inj₂ r) = inj₂ (ζ⁺ s t r)

ξ₁⁺ : (s t : Γ ⊢ σ ⇒ τ) (r : Γ ⊢ σ) → s ↝⁺ t → s ∙ r ↝⁺ t ∙ r
ξ₁⁺ s t r (↝lift s↝t) = ↝lift (ξ₁ s↝t)
ξ₁⁺ s t r (↝trans s↝r r↝⁺t) = ↝trans (ξ₁ s↝r) (ξ₁⁺ _ t r r↝⁺t)

ξ₁⋆ : (s t : Γ ⊢ σ ⇒ τ) (r : Γ ⊢ σ) → s ↝⋆ t → s ∙ r ↝⋆ t ∙ r
ξ₁⋆ s .s r (inj₁ refl) = inj₁ refl
ξ₁⋆ s t  r (inj₂ p)    = inj₂ (ξ₁⁺ s t r p)

ξ₂⁺ : (r : Γ ⊢ σ ⇒ τ) (s t : Γ ⊢ σ) → s ↝⁺ t → r ∙ s ↝⁺ r ∙ t
ξ₂⁺ r s t (↝lift s↝t)       = ↝lift (ξ₂ s↝t)
ξ₂⁺ r s t (↝trans s↝r r↝⁺t) = ↝trans (ξ₂ s↝r) (ξ₂⁺ r _ t r↝⁺t)

ξ₂⋆ : (r : Γ ⊢ σ ⇒ τ) (s t : Γ ⊢ σ) → s ↝⋆ t → r ∙ s ↝⋆ r ∙ t
ξ₂⋆ r s t (inj₁ refl) = inj₁ refl
ξ₂⋆ r s t (inj₂ y)    = inj₂ (ξ₂⁺ r s t y)

↝⁺-trans : {s t r : Γ ⊢ τ} → s ↝⁺ t → t ↝⁺ r → s ↝⁺ r
↝⁺-trans (↝lift r) s    = ↝trans r s
↝⁺-trans (↝trans r s) t = ↝trans r (↝⁺-trans s t)

↝⋆-trans : {s t r : Γ ⊢ τ} → s ↝⋆ t → t ↝⋆ r → s ↝⋆ r
↝⋆-trans (inj₁ refl) s           = s
↝⋆-trans r           (inj₁ refl) = r
↝⋆-trans (inj₂ r)    (inj₂ s)    = inj₂ (↝⁺-trans r s)

↝-subst : (t : Γ ⊢ τ) (σ σ' : Subst Γ Δ) → ({τ₂ : Type} (x : Γ ∋ τ₂) → σ x ≡ σ' x ⊎ σ x ↝⁺ σ' x) → subst σ t ≡ subst σ' t ⊎ subst σ t ↝⁺ subst σ' t
↝-subst (var x)   σ σ' p = p x
↝-subst (abs t)   σ σ' p = ζ⋆ _ _ (↝-subst t (exts σ) (exts σ') (ext-subst-red σ σ' p))
↝-subst (t₁ ∙ t₂) σ σ' p with ↝-subst t₁ σ σ' p | ↝-subst t₂ σ σ' p
... | p | q = ↝⋆-trans (ξ₁⋆ _ _ _ p) (ξ₂⋆ _ _ _ q)

SN-closed-β-expansion : (Γ : Ctx) (τ : Type) (t : Γ , σ ⊢ τ) (u : Γ ⊢ σ) → SN⁺ (t [ u ]) → SN u → SN (abs t ∙ u)
SN-closed-β-expansion-sn : (Γ : Ctx) (τ : Type) (t : Γ , σ ⊢ τ) (u : Γ ⊢ σ) → SN⁺ (t [ u ]) → SN u → (s : Γ ⊢ τ) → abs t ∙ u ↝ s → SN s

SN-closed-β-expansion Γ τ t u t[u]∈SN u∈SN = sn (SN-closed-β-expansion-sn Γ τ t u t[u]∈SN u∈SN)
SN-closed-β-expansion-sn Γ τ t u (sn t[u]∈SN) u∈SN      .(abs _ ∙ u) (ξ₁ (ζ r)) = SN-closed-β-expansion Γ τ _ u (t[u]∈SN _ (↝lift (subst-↝ _ _ r (substLast u)))) u∈SN
SN-closed-β-expansion-sn Γ τ t u t[u]∈SN      u∈SN      .(t [ u ])   β          = SN⁺⊆SN _ t[u]∈SN
SN-closed-β-expansion-sn Γ τ t u (sn t[u]∈SN) (sn u∈SN) .(abs t ∙ _) (ξ₂ {t' = u'} r)
  with ↝-subst t (substLast u) (substLast u') (λ { Z → inj₂ (↝lift r) ; (S x) → inj₁ refl })
... | inj₁ t[u]≡t[u']  = SN-closed-β-expansion Γ τ t u' (subst-≡ SN⁺ t[u]≡t[u'] (sn t[u]∈SN)) (u∈SN u' r)
... | inj₂ t[u]↝⁺t[u'] = SN-closed-β-expansion Γ τ t u' (t[u]∈SN (subst (substLast u') t) t[u]↝⁺t[u']) (u∈SN u' r)

module Neutral where
  -- when applied, these terms do not create new redexes
  data NE : Γ ⊢ τ → Set where
    var : (x : Γ ∋ τ) → NE (var x)
    _∙_ : {t : Γ ⊢ σ ⇒ τ} → NE t → {u : Γ ⊢ σ} → SN u → NE (t ∙ u)

  -- these terms are closed under reduction and more general are directly strongly normalizing
  -- because only one of the (by definition) already SN terms can normalize
  NE-closed-↝ : (t u : Γ ⊢ τ) → NE t → t ↝ u → NE u
  NE-closed-↝ .(_ ∙ _) .(_ ∙ _) (t∈NE ∙ s∈SN   ) (ξ₁ t↝u) = NE-closed-↝ _ _ t∈NE t↝u ∙ s∈SN
  NE-closed-↝ .(_ ∙ _) .(_ ∙ _) (t∈NE ∙ sn s∈SN) (ξ₂ t↝u) = t∈NE                     ∙ s∈SN _ t↝u

  -- we package the termination for pairs in a single type such that Agda recognises that a single argument 
  -- decreases in NE⊆SN-∙. 
  data SN-× (t : Γ ⊢ τ) (s : Γ ⊢ σ) : Set where
    sn-× : (∀ t′ → t ↝ t′ → SN-× t′ s) → (∀ s′ → s ↝ s′ → SN-× t s′) → SN-× t s
  
  sn-×-acc : (t : Γ ⊢ τ) (s : Γ ⊢ σ) → SN t → SN s → SN-× t s
  sn-×-acc t s p@(sn t∈SN) q@(sn s∈SN) = sn-× (λ t′ t↝t′ → sn-×-acc t′ s (t∈SN t′ t↝t′) q) (λ s′ s↝s′ → sn-×-acc t s′ p (s∈SN s′ s↝s′))
  
  NE⊆SN-∙ : (t : Γ ⊢ (τ ⇒ σ)) (s : Γ ⊢ τ) → NE t → SN-× t s → SN (t ∙ s)
  NE⊆SN-∙ t s t∈NE (sn-× p q) = sn λ where -- note that t∈NE limits the cases for ↝
    (u ∙ s) (ξ₁ t↝u) → NE⊆SN-∙ u s (NE-closed-↝ t u t∈NE t↝u) (p u t↝u)
    (t ∙ u) (ξ₂ u↝s) → NE⊆SN-∙ t u t∈NE                       (q u u↝s)
  
  NE⊆SN : (t : Γ ⊢ τ) → NE t → SN t
  NE⊆SN (var x) (var x) = sn λ where u ()
  NE⊆SN (t ∙ s) (t∈NE ∙ s∈SN) = NE⊆SN-∙ t s t∈NE (sn-×-acc t s (NE⊆SN t t∈NE) s∈SN)

  NE-closed-renaming : (t : Γ ⊢ τ) (ρ : Renaming Γ Δ) → NE t → NE (rename ρ t)
  NE-closed-renaming .(var x) ρ (var x) = var (ρ x)
  NE-closed-renaming .(_ ∙ _) ρ (t ∙ u) = NE-closed-renaming _ ρ t ∙ SN-closed-renaming← _ ρ _ u
open Neutral

module Log where
  ⟦_∶_⟧ : (Γ : Ctx) (τ : Type) → Γ ⊢ τ → Set
  ⟦ Γ ∶ ⋆ ⟧     t = SN t
  ⟦ Γ ∶ τ ⇒ σ ⟧ t = {Δ : Ctx} (ρ : Renaming Γ Δ) (u : Δ ⊢ τ) → ⟦ Δ ∶ τ ⟧ u → ⟦ Δ ∶ σ ⟧ (rename ρ t ∙ u)

  ⟦_⟧ : (Γ : Ctx) {Δ : Ctx} → Subst Γ Δ → Set
  ⟦ Γ ⟧ {Δ = Δ} ρ = {σ : Type} (x : Γ ∋ σ) → ⟦ Δ ∶ σ ⟧ (ρ x)

  -- immidiate relation between ⟦_⟧, SN and NE
  -- we prove them by mutual induction over the strucure of the type

  ⟦_∶_⟧⊆SN : (Γ : Ctx) (τ : Type) (t : Γ ⊢ τ) → ⟦ Γ ∶ τ ⟧ t → SN t
  NE⊆⟦_∶_⟧ :  (Γ : Ctx) (τ : Type) (t : Γ ⊢ τ) → NE t → ⟦ Γ ∶ τ ⟧ t 

  ⟦ Γ ∶ ⋆ ⟧⊆SN t t∈SN = t∈SN
  ⟦ Γ ∶ τ ⇒ σ ⟧⊆SN t t∈⟦τ⇒σ⟧ = SN-closed-renaming Γ S_ t tρ∈SN
    where
      t0∈⟦σ⟧ : ⟦ Γ , τ ∶ σ ⟧ (rename S_ t ∙ var Z)
      t0∈⟦σ⟧ = t∈⟦τ⇒σ⟧ S_ (var Z) (NE⊆⟦ Γ , τ ∶ τ ⟧ (var Z) (var Z))

      t0∈SN : SN (rename S_ t ∙ var Z)
      t0∈SN = ⟦ Γ , τ ∶ σ ⟧⊆SN (rename S_ t ∙ var Z) t0∈⟦σ⟧

      tρ∈SN : SN (rename S_ t)
      tρ∈SN = tu∈SN⇒t∈SN (rename S_ t) (var Z) t0∈SN

  NE⊆⟦ Γ ∶ ⋆ ⟧ t t∈NE = NE⊆SN t t∈NE
  NE⊆⟦ Γ ∶ τ ⇒ σ ⟧ t t∈NE ρ u u∈⟦Δ∶τ⟧ = NE⊆⟦ _ ∶ σ ⟧ (rename ρ t ∙ u) (NE-closed-renaming t ρ t∈NE ∙ ⟦ _ ∶ τ ⟧⊆SN u u∈⟦Δ∶τ⟧)

  -- closure properties of ⟦_⟧
  ⟦_∶_⟧-closed-renaming :  (Γ : Ctx) (τ : Type) (t : Γ ⊢ τ) (ρ : Renaming Γ Δ) → ⟦ Γ ∶ τ ⟧ t → ⟦ Δ ∶ τ ⟧ (rename ρ t)
  ⟦ Γ ∶ ⋆ ⟧-closed-renaming t ρ t∈SN = SN-closed-renaming← _ ρ t t∈SN
  ⟦ Γ ∶ τ ⇒ σ ⟧-closed-renaming t ρ t∈⟦Γ∶τ⇒σ⟧ {Ω} γ u u∈⟦Ω∶τ⟧ = subst-≡ (λ x → ⟦ Ω ∶ σ ⟧ (x ∙ _)) (rename-∘ γ ρ t) (t∈⟦Γ∶τ⇒σ⟧ (γ ∘ ρ) u u∈⟦Ω∶τ⟧)

  infix 5 _↝ʷ_
  data _↝ʷ_ : Γ ⊢ τ → Γ ⊢ τ → Set where
      ξ₁ : {s s' : Γ ⊢ σ ⇒ τ} {t  : Γ ⊢ σ}
         → s ↝ʷ s'
         → s ∙ t ↝ʷ s' ∙ t
    
      β : {s : Γ , σ ⊢ τ} {t : Γ ⊢ σ}
        → abs s ∙ t ↝ʷ s [ t ]

  rename-↝ʷ : (t u : Γ ⊢ τ) (ρ : Renaming Γ Δ) → t ↝ʷ u → rename ρ t ↝ʷ rename ρ u
  rename-↝ʷ .(_ ∙ _)    .(_ ∙ _)   ρ (ξ₁ t↝u) = ξ₁ (rename-↝ʷ _ _ ρ t↝u)
  rename-↝ʷ (abs t ∙ u) .(t [ u ])  ρ β       = subst-≡ (abs (rename (ext ρ) t) ∙ rename ρ u ↝ʷ_) (sym (rename-∘-[] ρ t u)) β

  conf-β-ξ₁ : (t₁ t₁′ : Γ , τ ⊢ σ) (t₂ : Γ ⊢ τ) → t₁ ↝ t₁′ → Σ[ w ∈ Γ ⊢ σ ] (abs t₁′ ∙ t₂ ↝ʷ w × t₁ [ t₂ ] ↝⋆ w)
  conf-β-ξ₁ t₁ t₁′ t₂ x = ⟨ t₁′ [ t₂ ] , ⟨ β , inj₂ (↝lift (subst-↝ t₁ t₁′ x (substLast t₂))) ⟩ ⟩

  conf-β-ξ₂ : (t₁ : Γ , τ ⊢ σ) (t₂ t₂′ : Γ ⊢ τ) → t₂ ↝ t₂′ → Σ[ w ∈ Γ ⊢ σ ] (abs t₁ ∙ t₂′ ↝ʷ w × t₁ [ t₂ ] ↝⋆ w)
  conf-β-ξ₂ t₁ t₂ t₂′ x = ⟨ t₁ [ t₂′ ] , ⟨ β , ↝-subst t₁ (substLast t₂) (substLast t₂′) (λ { Z → inj₂ (↝lift x) ; (S x) → inj₁ refl }) ⟩ ⟩

  -- Lemma 4
  ↝ʷ-↝-pseudo-locally-confluent : (t t′ t″ : Γ ⊢ σ) → t ↝ʷ t′ → t ↝ t″ → t′ ≡ t″ ⊎ Σ[ w ∈ Γ ⊢ σ ] (t″ ↝ʷ w × t′ ↝⋆ w)
  ↝ʷ-↝-pseudo-locally-confluent .(_ ∙ _)     .(_ ∙ _)   .(_ ∙ _) (ξ₁ r) (ξ₁ s) with ↝ʷ-↝-pseudo-locally-confluent _ _ _ r s
  ... | inj₁ refl = inj₁ refl
  ... | inj₂ ⟨ w , ⟨ r , s ⟩ ⟩ = inj₂ ⟨ w ∙ _ , ⟨ ξ₁ r , ξ₁⋆ _ w _ s ⟩ ⟩
  ↝ʷ-↝-pseudo-locally-confluent .(_ ∙ _) .(_ ∙ _) .(_ ∙ _) (ξ₁ r) (ξ₂ s) = inj₂ ⟨ _ ∙ _ , ⟨ ξ₁ r , inj₂ (↝lift (ξ₂ s)) ⟩ ⟩
  ↝ʷ-↝-pseudo-locally-confluent .(abs t₁ ∙ t₂) .(t₁ [ t₂ ]) .(t₁ [ t₂ ])  (β {σ = σ} {τ = τ} {s = t₁} {t = t₂}) β          = inj₁ refl
  ↝ʷ-↝-pseudo-locally-confluent .(abs t₁ ∙ t₂) .(t₁ [ t₂ ]) .(abs _ ∙ t₂) (β {σ = σ} {τ = τ} {s = t₁} {t = t₂}) (ξ₁ (ζ s)) = inj₂ (conf-β-ξ₁ t₁ _ t₂ s)
  ↝ʷ-↝-pseudo-locally-confluent .(abs t₁ ∙ t₂) .(t₁ [ t₂ ]) .(abs t₁ ∙ _) (β {σ = σ} {τ = τ} {s = t₁} {t = t₂}) (ξ₂ s)     = inj₂ (conf-β-ξ₂ t₁ t₂ _ s)

  data SN⁺-× (t : Γ ⊢ τ) (s : Γ ⊢ σ) : Set where
    sn-× : ({t′ : Γ ⊢ τ} {s′ : Γ ⊢ σ} → t ↝ t′ → s ↝⋆ s′ → SN⁺-× t′ s′)
         → ({s′ : Γ ⊢ σ} → s ↝⁺ s′ → SN⁺-× t s′)
         → SN⁺-× t s

  SN⁺-×-acc : {t : Γ ⊢ τ} {s : Γ ⊢ σ} → SN t → SN⁺ s → SN⁺-× t s
  SN⁺-×-acc (sn p) (sn q) = sn-×
    (λ where
      t↝t′ (inj₁ refl) → SN⁺-×-acc (p _ t↝t′) (sn q)
      t↝t′ (inj₂ s↝s′) → SN⁺-×-acc (p _ t↝t′) (q _ s↝s′))
    (λ s↝⁺s' → SN⁺-×-acc (sn p) (q _ s↝⁺s'))

  SN⁺-×⊆SN : {t : Γ ⊢ τ} {s : Γ ⊢ σ} → SN⁺-× s t → SN t
  SN⁺-×⊆SN (sn-× _ p) = sn λ s t↝s → SN⁺-×⊆SN (p (↝lift t↝s))

  -- Lemma 3
  SN-closed-backwards-↝ʷ-wf : (t t' : Γ ⊢ σ ⇒ τ) (u : Γ ⊢ σ) → SN⁺-× t (t' ∙ u) → t ↝ʷ t' → SN (t ∙ u)
  SN-closed-backwards-↝ʷ-wf t t′ u p@(sn-× t∈SN t'u∈SN) t↝ʷt′ = sn λ where
    (t″ ∙ u) (ξ₁ t↝t″) → case ↝ʷ-↝-pseudo-locally-confluent t t′ t″ t↝ʷt′ t↝t″ of λ where
      (inj₁ refl) → SN⁺-×⊆SN p
      (inj₂ ⟨ w , ⟨ t″↝ʷw , t′↝⋆w ⟩ ⟩) → SN-closed-backwards-↝ʷ-wf t″ w u (t∈SN t↝t″ (ξ₁⋆ t′ w u t′↝⋆w)) t″↝ʷw
    (t ∙ u′) (ξ₂ u↝u′) → SN-closed-backwards-↝ʷ-wf t t′ u′ (t'u∈SN (↝lift (ξ₂ u↝u′))) t↝ʷt′

  SN-closed-backwards-↝ʷ : (t t' : Γ ⊢ σ ⇒ τ) (u : Γ ⊢ σ) → SN t → SN (t' ∙ u) → t ↝ʷ t' → SN (t ∙ u)
  SN-closed-backwards-↝ʷ t t′ u t∈SN t'u∈SN t↝ʷt′ = SN-closed-backwards-↝ʷ-wf t t′ u (SN⁺-×-acc t∈SN (SN⊆SN⁺ _ t'u∈SN)) t↝ʷt′

  -- Proposition 3
  ⟦_∶_⟧-closed-↝ʷ-backwards-red : (Γ : Ctx) (σ : Type) (t t' : Γ ⊢ σ) → ⟦ Γ ∶ σ ⟧ t' → t ↝ʷ t' → SN t → ⟦ Γ ∶ σ ⟧ t
  ⟦ Γ ∶ ⋆ ⟧-closed-↝ʷ-backwards-red t t' t'∈⟦Γ∶σ⟧ t↝ʷt' t∈SN = t∈SN
  ⟦ Γ ∶ σ ⇒ τ ⟧-closed-↝ʷ-backwards-red t t' t'∈⟦Γ∶σ⇒τ⟧ t↝ʷt' t∈SN ρ u u∈⟦Δ∶σ⟧ =
    ⟦ _ ∶ τ ⟧-closed-↝ʷ-backwards-red (rename ρ t ∙ u) (rename ρ t' ∙ u) (t'∈⟦Γ∶σ⇒τ⟧ ρ u u∈⟦Δ∶σ⟧) (ξ₁ (rename-↝ʷ t t' ρ t↝ʷt'))
      (SN-closed-backwards-↝ʷ (rename ρ t) (rename ρ t') u (SN-closed-renaming← Γ ρ t t∈SN) (⟦ _ ∶ τ ⟧⊆SN (rename ρ t' ∙ u) (t'∈⟦Γ∶σ⇒τ⟧ ρ u u∈⟦Δ∶σ⟧)) (rename-↝ʷ t t' ρ t↝ʷt'))

  ⟦_∶_⟧-closed-under-β-exp : (Γ : Ctx) (τ : Type) (t : Γ , σ ⊢ τ) (u : Γ ⊢ σ) → SN u → ⟦ Γ ∶ τ ⟧ (t [ u ]) → ⟦ Γ ∶ τ ⟧ (abs t ∙ u)
  ⟦ Γ ∶ τ ⟧-closed-under-β-exp t u u∈SN t[u]∈⟦Γ∶τ⟧ = ⟦ Γ ∶ τ ⟧-closed-↝ʷ-backwards-red (abs t ∙ u) (t [ u ]) t[u]∈⟦Γ∶τ⟧ β
    (SN-closed-β-expansion Γ τ t u (SN⊆SN⁺ _ (⟦ Γ ∶ τ ⟧⊆SN _ t[u]∈⟦Γ∶τ⟧)) u∈SN)

  theorem : (t : Γ ⊢ τ) (γ : Subst Γ Δ) → ⟦ Γ ⟧ γ → ⟦ Δ ∶ τ ⟧ (subst γ t)
  theorem (var x) γ γ∈⟦Γ⟧ = γ∈⟦Γ⟧ x
  theorem (t ∙ u) γ γ∈⟦Γ⟧ = subst-≡ (λ x → ⟦ _ ∶ _ ⟧ (x ∙ _)) (rename-id (subst γ t)) (theorem t γ γ∈⟦Γ⟧ id (subst γ u) (theorem u γ γ∈⟦Γ⟧))
  theorem {Γ = Γ} {τ = τ ⇒ σ} {Δ = Ω} (abs t) γ γ∈⟦Γ⟧ {Δ} ρ u u∈⟦Δ:σ⟧ = ⟦ Δ ∶ σ ⟧-closed-under-β-exp (rename (ext ρ) (subst (exts γ) t)) u (⟦ Δ ∶ τ ⟧⊆SN u u∈⟦Δ:σ⟧) t[u]γ∈⟦Δ∶σ⟧
    where
      γ' : Subst (Γ , τ) Δ
      γ' Z     = u
      γ' (S x) = rename ρ (γ x)

      γ'∈⟦Γ⟧ : ⟦ Γ , τ ⟧ γ'
      γ'∈⟦Γ⟧ Z     = u∈⟦Δ:σ⟧
      γ'∈⟦Γ⟧ (S x) = ⟦ Ω ∶ _ ⟧-closed-renaming (γ x) ρ (γ∈⟦Γ⟧ x)

      γ'≡ρ∘γ∘[u] : subst γ' t ≡ rename (ext ρ) (subst (exts γ) t) [ u ]
      γ'≡ρ∘γ∘[u] =
          begin
            subst γ' t
          ≡⟨ cong {A = Subst _ _} (λ - → subst - t) (substExt _ _ λ{ Z → refl ; (S x) →
              begin
                rename ρ (γ x)
              ≡⟨ cong (rename ρ) (sym (subst-id (γ x))) ⟩
                rename ρ (subst idˢ (γ x))
              ≡⟨ rename-subst ρ _ (γ x) ⟩
                subst (λ z → var (ρ z)) (γ x)
              ≡⟨ subst-rename _ S_ (γ x) ⟩
                subst _ (rename S_ (γ x))
              ∎ }) ⟩
            subst (λ s → subst _ (exts γ s)) t
          ≡⟨ subst-∘ _ _ t ⟩
            subst (λ z → _) (subst (exts γ) t)
          ≡⟨ subst-rename _ _ (subst (exts γ) t) ⟩
            rename (ext ρ) (subst (exts γ) t) [ u ]
          ∎

      -- for this substitution, we can use the IH
      tγ'∈⟦Δ∶σ⟧ : ⟦ Δ ∶ σ ⟧ (subst γ' t)
      tγ'∈⟦Δ∶σ⟧ = theorem t γ' γ'∈⟦Γ⟧

      -- this corresponds already to the fact we wanted to show
      t[u]γ∈⟦Δ∶σ⟧ : ⟦ Δ ∶ σ ⟧ (rename (ext ρ) (subst (exts γ) t) [ u ])
      t[u]γ∈⟦Δ∶σ⟧ = subst-≡ ⟦ Δ ∶ σ ⟧ γ'≡ρ∘γ∘[u] tγ'∈⟦Δ∶σ⟧

  id∈⟦Γ⟧ : ⟦ Γ ⟧ var
  id∈⟦Γ⟧ x = NE⊆⟦ _ ∶ _ ⟧ (var x) (var x)
open Log


module No where
  t∈SN : (t : Γ ⊢ τ) → SN t
  t∈SN {Γ = Γ} {τ = τ} t = subst-≡ SN (subst-id t) (⟦ Γ ∶ τ ⟧⊆SN (subst var t) (theorem t var id∈⟦Γ⟧))

  ↝-wf : WellFounded (λ s t → _↝_ {Γ = Γ} {τ = τ} t s)
  ↝-wf t = t∈SN⇒↝-WF t (t∈SN t)
