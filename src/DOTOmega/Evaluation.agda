open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Evaluation {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.List
open import Data.Product using (_×_; _,_)

open import DOTOmega.Syntax TypeL TermL

open import Data.Var
open import Data.Context

Stack = Ctx Val

infix 4 _⇒_

data _⇒_ : Stack × Term → Stack × Term → Set where
  ⇒-sel : ∀{E x M τ ds t} →
    E [ x ]⊢>(new τ ds) →
    (val M =' t) ∈ map (plugDefn (Free x)) ds →
    (E , (Free x) ∙ M) ⇒ (E , t)
  ⇒-app : ∀{E f x τ e} →
    E [ f ]⊢>(ƛ τ e) →
    (E , Free f ⊡ x) ⇒ (E , plugTerm x e)
  ⇒-let-val : ∀{E x v e} →
    (E , let' V v in' e) ⇒ (E & x ~ v , openTerm x e)
  ⇒-let-var : ∀{E y e} →
    (E , let' ` (Free y) in' e) ⇒ (E , plugTerm (Free y) e)
  ⇒-let-inner : ∀{E E' e₀ e₀' e} →
    (E , e₀) ⇒ (E' , e₀') →
    (E , let' e₀ in' e) ⇒ (E' , let' e₀' in' e)

infix 5 _normal

data _normal : Term → Set where
  var-normal : ∀{x} → ` x normal
  val-normal : ∀{v} → V v normal

