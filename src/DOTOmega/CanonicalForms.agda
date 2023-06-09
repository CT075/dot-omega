open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.CanonicalForms
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Data.Var
open import Data.Context

open import DOTOmega.Syntax TypeL TermL renaming (_∈_ to _∈def_)
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Properties TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL
open import DOTOmega.Evaluation TypeL TermL

{-
ℿ→Γ[x] : ∀{Γ f S T} →
  Γ inert-ctx →
  Γ ⊢tm ` (Free f) ∈ ℿ S T →
  Σ[ τ ∈ Type ](Γ [ f ]⊢> Ty τ)
-}

{-
canonical-ℿ : ∀{Γ E f S T} →
  Γ inert-ctx →
  Γ ⊨ E →
  Γ ⊢tm ` (Free f) ∈ ℿ S T →
  Σ[ S'e ∈ Type × Term ](E [ f ]⊢> ƛ (proj₁ S'e) (proj₂ S'e))
canonical-ℿ Γinert Γ⊨E Γ⊢f∈ℿST = {!!}
-}
