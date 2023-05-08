open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Soundness
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.String using (String)
open import Data.List
open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Data.Context

open import DOTOmega.Syntax TypeL TermL renaming (_∈_ to _∈def_)
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL
open import DOTOmega.Evaluation TypeL TermL

infix 4 _⊨_

termVars : Context → List String
termVars [] = []
termVars ((E x (Ty _)) ∷ Γ) = x ∷ termVars Γ
termVars ((E x (Kd _)) ∷ Γ) = termVars Γ

record _⊨_ (Γ : Context) (E : Stack) : Set where
  field
    same-dom : termVars Γ ≡ domain E
    binding-valid : ∀{x τ v} →
      Γ [ x ]⊢> Ty τ →
      E [ x ]⊢> v →
      Γ ⊢tm V v ∈ τ

infix 4 ⊢ev_∈_

data ⊢ev_∈_ : Stack × Term → Type → Set where
  tyval-ctx : ∀{Γ E e τ} →
    Γ inert-ctx →
    Γ ⊨ E →
    Γ ⊢tm e ∈ τ →
    ⊢ev (E , e) ∈ τ

postulate
  value-typing : ∀ {Γ v τ} →
    Γ ⊢tm V v ∈ τ →
    Σ[ τ' ∈ Type ](Γ ⊢!val v ∈ τ' × Γ ⊢ty τ' ≤ τ ∈ ✶)

preservation : ∀ {E e E' e' τ} →
  ⊢ev (E , e) ∈ τ →
  (E , e) ⇒ (E' , e') →
  ⊢ev (E' , e') ∈ τ
preservation = {!!}

progress : ∀ {E e τ} →
  ⊢ev (E , e) ∈ τ →
  e normal ⊎ (Σ[ st ∈ (Stack × Term) ]((E , e) ⇒ st))
progress = {!!}
