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
  μ-norm : ∀{A} → μ A normal
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

⟨_,_⟩∈⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈⟦ K ⟧ = denot-step ValS Γ τ K (<kd×lr-wf (K , ValS))

⟨_,_⟩∈ℰ⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , τ ⟩∈ℰ⟦ K ⟧ = denot-step EvalS Γ τ K (<kd×lr-wf (K , EvalS))

strong-normalization : ∀ {Γ A K} → Γ inert-ctx → Γ ⊢#ty A ∈ K → ⟨ Γ , A ⟩∈ℰ⟦ K ⟧
strong-normalization Γinert (k-var-# Γctx Γ[x]⊢>K) = {! !}
strong-normalization Γinert k-top-# =
  (⊤ , ty-refl k-top-# , ⊤-norm , st-bot-# k-top-# , st-top-# k-top-#)
strong-normalization Γinert k-bot-# =
  (⊥ , ty-refl k-bot-# , ⊥-norm , st-bot-# k-bot-# , st-top-# k-bot-#)
strong-normalization Γinert (k-sing-# Γ⊢#A∈S∙∙U) =
  let (τ , Γ⊢#tyA==τ , τ-norm , S≤τ , τ≤U) = strong-normalization Γinert Γ⊢#A∈S∙∙U
   in
  (τ , {!!} , τ-norm , {!!} , {!!})
strong-normalization Γinert (k-arr-# Γ⊢#A∈✶ Γx∶A⊢#B∈✶) = {! !}
strong-normalization Γinert (k-abs-# Γ⊢#J-kd Γx∶J⊢#K-kd) = {! !}
strong-normalization Γinert (k-app-# Γ⊢#f∈ℿJK Γ⊢#B∈J) =
  let (ƛJ'A , Γ⊢#f==ƛJ'A , ⟨Γ,ƛJ'A⟩∈⟦ℿJK⟧) = strong-normalization Γinert Γ⊢#f∈ℿJK
      (τ , Γ⊢#B==τ , ⟨Γ,τ⟩∈⟦J⟧) = strong-normalization Γinert Γ⊢#B∈J
   in
  {!!}
strong-normalization Γinert (k-intersect-# Γ⊢#τ₁∈S₁∙∙U₁ Γ⊢#τ₂∈S₂∙∙U₂) = {! !}
strong-normalization Γinert (k-sub-# Γ⊢#A∈J Γ⊢#J≤K) = {! !}
strong-normalization Γinert (k-field-# Γ⊢#τ∈S∙∙U) = {! !}
strong-normalization Γinert (k-typ-# Γ⊢#K-kd) = {! !}
strong-normalization Γinert (k-sel-# Γ⊢!x∈U⟫[typ-A∶S[τ∈K]]) = {! !}
