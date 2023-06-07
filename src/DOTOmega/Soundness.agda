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

open import Data.Var
open import Data.Context renaming (E to E_)

open import DOTOmega.Syntax TypeL TermL renaming (_∈_ to _∈def_)
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Properties TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL
open import DOTOmega.Typing.Precise TypeL TermL
open import DOTOmega.Evaluation TypeL TermL

infix 4 _⊨_

termVars : Context → List String
termVars [] = []
termVars ((E_ x (Ty _)) ∷ Γ) = x ∷ termVars Γ
termVars ((E_ x (Kd _)) ∷ Γ) = termVars Γ

record _⊨_ (Γ : Context) (E : Stack) : Set where
  field
    same-dom : termVars Γ ≡ domain E
    binding-valid : ∀{x τ v} →
      Γ [ x ]⊢> Ty τ →
      E [ x ]⊢> v →
      Γ ⊢tm V v ∈ τ

infix 4 ⊢ev⟨_,_⟩∈_

record ⊢ev⟨_,_⟩∈_ (E : Stack) (e : Term) (τ : Type) : Set where
  constructor ev-type
  field
    Gamma : Context
    Gamma-inert : Gamma inert-ctx
    Gamma⊨E : Gamma ⊨ E
    Gamma⊢e∈τ : Gamma ⊢tm e ∈ τ

value-typing : ∀ {Γ v τ} →
  Γ ⊢tm V v ∈ τ →
  Σ[ τ' ∈ Type ](Γ ⊢!val v ∈ τ' × Γ ⊢ty τ' ≤ τ ∈ ✶)
value-typing {τ = τ} Γ⊢v∈S@(ty-ℿ-intro Γx⊢xe∈xρ) =
  (τ , fun-I-! Γx⊢xe∈xρ , st-refl (typing-validity Γ⊢v∈S))
value-typing {τ = τ} Γ⊢v∈S@(ty-new-intro Γx⊢ds∈xτ) =
  (τ , rec-I-! Γx⊢ds∈xτ , st-refl (typing-validity Γ⊢v∈S))
value-typing (ty-sub Γ⊢v∈S S≤U) =
  let (τ , Γ⊢!v∈τ , τ≤S) = value-typing Γ⊢v∈S
   in (τ , Γ⊢!v∈τ , st-trans τ≤S S≤U)

postulate
  canonical-ℿ : ∀{Γ E f S T} →
    Γ inert-ctx →
    Γ ⊨ E →
    Γ ⊢tm ` (Free f) ∈ ℿ S T →
    Σ[ S'e ∈ Type × Term ](E [ f ]⊢> ƛ (proj₁ S'e) (proj₂ S'e))

progress : ∀ {E e τ} →
  ⊢ev⟨ E , e ⟩∈ τ →
  e normal ⊎ (Σ[ st ∈ (Stack × Term) ]((E , e) ⇒ st))
progress {E = E} (ev-type Γ Γinert Γ⊨E Γ⊢e∈τ) = progress-impl Γ⊢e∈τ
  where
    progress-impl : ∀{e τ} → Γ ⊢tm e ∈ τ →
      e normal ⊎ (Σ[ st ∈ (Stack × Term) ]((E , e) ⇒ st))
    progress-impl (ty-var _) = inj₁ var-normal
    progress-impl (ty-ℿ-intro Γx⊢xe∈τ) = inj₁ val-normal
    progress-impl (ty-ℿ-elim {fv} {x} {S} {T} Γ⊢fv∈ℿST Γ⊢x∈S)
      with typed-var-is-free Γ⊢fv∈ℿST
    ... | (f , refl) =
      let ((S' , e) , E[f]⊢>ƛS'e) = canonical-ℿ Γinert Γ⊨E Γ⊢fv∈ℿST
       in inj₂ ((E , plugTerm x e) , ⇒-app E[f]⊢>ƛS'e)
    progress-impl (ty-new-intro Γx⊢ds∈xτ) = inj₁ val-normal
    progress-impl (ty-new-elim Γ⊢x∈[ℓ∶τ]) = {! !}
    progress-impl (ty-let {e₁} {e₂} {x} Γ⊢e₁∈τ₁ Γ⊢e₂∈τ₂) with progress-impl Γ⊢e₁∈τ₁
    ... | inj₁ (var-normal {x}) = inj₂ ((E , plugTerm x e₂) , ⇒-let-var)
    ... | inj₁ (val-normal {v}) = inj₂ ((E & x ~ v , openTerm x e₂) , ⇒-let-val)
    ... | inj₂ ((E' , e₁') , ⟨E,e₁⟩⇒⟨E',e₁'⟩) =
      inj₂ ((E' , let' e₁' in' e₂) , ⇒-let-inner ⟨E,e₁⟩⇒⟨E',e₁'⟩)
    progress-impl (ty-rec-intro Γ⊢x∈xτ) = inj₁ var-normal
    progress-impl (ty-rec-elim Γ⊢x∈μτ) = inj₁ var-normal
    progress-impl (ty-and-intro Γ⊢e∈S Γ⊢e∈U) = progress-impl Γ⊢e∈S
    progress-impl (ty-sub Γ⊢e∈S S≤U) = progress-impl Γ⊢e∈S

preservation : ∀ {E e E' e' τ} →
  ⊢ev⟨ E , e ⟩∈ τ →
  (E , e) ⇒ (E' , e') →
  ⊢ev⟨ E' , e' ⟩∈ τ
preservation = {!!}
