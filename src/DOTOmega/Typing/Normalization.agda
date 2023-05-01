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
denot-step ValS Γ A (ℿ J K) (acc rec) = Void
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

mutual
  data ⟨_,_⟩∈⟦_⟧ : Context → Type → Kind → Set where
    denot-intv : ∀{Γ τ S U} →
      τ normal →
      Γ ⊢#ty S ≤ τ ∈ ✶ →
      Γ ⊢#ty τ ≤ U ∈ ✶ →
      ⟨ Γ , τ ⟩∈⟦ S ∙∙ U ⟧
    denot-abs : ∀{Γ} {J J' : Kind} {K : Kind} {A} →
      Γ ⊢#kd J ≤ J' →
      (∀ τ x →
        Σ[ rec ∈ WfRec _<kd×lr_ (Acc _<kd×lr_) (ℿ J K , ValS) ](denot-step ValS Γ τ J (rec _ (inj₁ (<kd-ℿ₁ J K)))
        → ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧)) →
      ⟨ Γ , ƛ J' A ⟩∈⟦ ℿ J K ⟧

  data ⟨_,_⟩∈ℰ⟦_⟧ : Context → Type → Kind → Set where
    eval : ∀{Γ A τ K} → Γ ⊢#ty A == τ ∈ K → ⟨ Γ , τ ⟩∈⟦ K ⟧ → ⟨ Γ , A ⟩∈ℰ⟦ K ⟧

mutual
  denot-ind-rec-v : ∀{Γ τ K acc} → denot-step ValS Γ τ K acc → ⟨ Γ , τ ⟩∈⟦ K ⟧
  denot-ind-rec-v {K = S ∙∙ U} {acc = acc _} (τ-normal , S≤τ , τ≤U) =
    denot-intv τ-normal S≤τ τ≤U
  denot-ind-rec-v {Γ} {ƛ J' A} {ℿ J K} {acc = acc rec} (J≤J' , f) = denot-abs J≤J' f'
    where
      f' : ∀ τ x →
        Σ[ rec ∈ WfRec _<kd×lr_ _ (ℿ J K , ValS) ](denot-step ValS Γ τ J (rec _ (inj₁ (<kd-ℿ₁ J K)))
        → ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧)
      f' τ x = (rec , λ ⟨Γ,τ⟩∈'⟦J⟧ → denot-ind-rec-e (f τ x ⟨Γ,τ⟩∈'⟦J⟧))

  denot-ind-rec-e : ∀{Γ A K acc} → denot-step EvalS Γ A K acc → ⟨ Γ , A ⟩∈ℰ⟦ K ⟧
  denot-ind-rec-e {acc = acc _} (τ , A==τ , ⟨Γ,τ⟩∈'⟦K⟧) =
    eval {τ = τ} A==τ (denot-ind-rec-v ⟨Γ,τ⟩∈'⟦K⟧)
