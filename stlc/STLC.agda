{-# OPTIONS --without-K #-}

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

