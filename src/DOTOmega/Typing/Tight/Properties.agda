open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Tight.Properties
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality

open import DOTOmega.Syntax TypeL TermL hiding (_∉_; _∈_)
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Inertness TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL

open import Data.Context

postulate
  plug-recd : ∀ {z τ} → τ recd → plugType z τ recd

  sing-sub : ∀{Γ τ k} → Γ ⊢ty τ ∈ k → Γ ⊢kd S[ τ ∈ k ] ≤ k

  sing-sub-# : ∀{Γ τ k} → Γ ⊢#ty τ ∈ k → Γ ⊢#kd S[ τ ∈ k ] ≤ k

  sing-idempotent : ∀ τ K → S[ τ ∈ S[ τ ∈ K ] ] ≡ S[ τ ∈ K ]

  sing-inert : ∀ τ k → S[ τ ∈ k ] inert-kd

  sing-trans-#-l : ∀{Γ τ K J} → Γ ⊢#kd K ≤ J → Γ ⊢#kd S[ τ ∈ K ] ≤ S[ τ ∈ J ]

  sk-trans-# : ∀{Γ J K L} → Γ ⊢#kd J ≤ K → Γ ⊢#kd K ≤ L → Γ ⊢#kd J ≤ L

  -- probably need kind validity here as well
  sk-refl-# : ∀{Γ} K → Γ ⊢#kd K ≤ K

  types-wf-# : ∀{Γ t τ} → Γ ⊢#tm t ∈ τ → Σ[ K ∈ Kind ] (Γ ⊢#ty τ ∈ K)

  ty-refl-# : ∀{Γ A K} → Γ ⊢#ty A ∈ K → Γ ⊢#ty A == A ∈ K

  -- TODO: is this even true?
  proper-types-equality-# :
    ∀{Γ A B S U} → Γ ⊢#ty A == B ∈ S ∙∙ U → Γ ⊢#ty A == B ∈ ✶

  eq-narrow-# : ∀{Γ A B K} → Γ ⊢#ty A == B ∈ K → Γ ⊢#ty A == B ∈ S[ A ∈ K ]

eq-left-# : ∀{Γ A B K} → Γ ⊢#ty A == B ∈ K → Γ ⊢#ty A ≤ B ∈ K
eq-left-# (st-antisym-# A≤B B≤A) = A≤B

eq-right-# : ∀{Γ A B K} → Γ ⊢#ty A == B ∈ K → Γ ⊢#ty B ≤ A ∈ K
eq-right-# (st-antisym-# A≤B B≤A) = B≤A

eq-refl-# : ∀{Γ A K} → Γ ⊢#ty A ∈ K → Γ ⊢#ty A == A ∈ K
eq-refl-# Γ⊢#A∈K = st-antisym-# (st-refl-# Γ⊢#A∈K) (st-refl-# Γ⊢#A∈K)
