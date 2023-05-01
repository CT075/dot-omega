open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Normalization
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Nat.Properties using (<-trans)
open import Data.Sum
open import Data.Product
open import Data.Empty renaming (⊥ to Void)
open import Relation.Binary.PropositionalEquality hiding (J)
open import Induction
open import Induction.WellFounded
open import Induction.Extensions

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL

open import Data.Context

infix 4 _normal

data _normal : Type → Set where
  ⊤-norm : ⊤ normal
  ⊥-norm : ⊥ normal
  ℿ-norm : ∀{τ e} → ƛ τ e normal
  ƛ-norm : ∀{K A} → ƛ K A normal
  ∧-norm : ∀{S U} → S normal → U normal → S ∧ U normal
  μ-norm : ∀{A} → A normal → μ A normal
  typdecl-norm : ∀{K M} → [ typ M ∶ K ] normal
  valdecl-norm : ∀{ℓ A} → A normal → [ val ℓ ∶ A ] normal

data LRSort : Set where
  ValS : LRSort
  EvalS : LRSort

data _<lr_ : LRSort → LRSort → Set where
  ValS<EvalS : ValS <lr EvalS

<lr-wf : ∀ t → Acc _<lr_ t
<lr-wf ValS = acc (λ _ ())
<lr-wf EvalS = acc (λ where ValS _ → acc (λ _ ()))

_<kd×lr_ = <-lex _<kd_ _<lr_
<kd×lr-wf = <-lex-wf <kd-wf <lr-wf

denot-step :
  (lr : LRSort) →
  Context →
  Type →
  (K : Kind) →
  Acc _<kd×lr_ (K , lr) →
  Set
denot-step ValS Γ τ (S ∙∙ U) (acc rec) =
  τ normal ×
  Γ ⊢#ty S ≤ τ ∈ ✶ ×
  Γ ⊢#ty τ ≤ U ∈ ✶
denot-step ValS Γ (ƛ J' A) (ℿ J K) (acc rec) =
    Γ ⊢#kd J ≤ J' ×
    (∀ τ x →
      denot-step ValS Γ τ J (rec _ (inj₁ (<kd-ℿ₁ J K))) →
      denot-step EvalS (Γ & x ~ Kd S[ τ ∈ J ]) A (openKind x K)
        (rec _ (inj₁ (<kd-ℿ-open x J K))))
denot-step ValS _ _ (ℿ J K) (acc rec) = Void
denot-step EvalS Γ A K (acc rec) =
  Σ[ τ ∈ Type ](
    Γ ⊢#ty A == τ ∈ K ×
    (denot-step ValS Γ τ K (rec _ (inj₂ (refl , ValS<EvalS)))))

denot : LRSort → Context → Type → Kind → Set
denot lr Γ τ K = denot-step lr Γ τ K (<kd×lr-wf (K , lr))

⟨_,_⟩∈'⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈'⟦ K ⟧ = denot ValS Γ τ K

⟨_,_⟩∈'ℰ⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈'ℰ⟦ K ⟧ = denot EvalS Γ τ K
