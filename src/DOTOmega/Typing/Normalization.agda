open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Normalization
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.List using (List; [])
open import Data.String using (String)

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
open import DOTOmega.Typing.Inertness TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL
open import DOTOmega.Typing.Tight.Properties TypeL TermL

open import Data.Var
open import Data.Context

infix 4 _whnf

data _whnf : Type → Set where
  ⊤-whnf : ⊤ whnf
  ⊥-whnf : ⊥ whnf
  ℿ-whnf : ∀{S T} → ℿ S T whnf
  ƛ-whnf : ∀{K A} → ƛ K A whnf
  ∧-whnf : ∀{S U} → S whnf → U whnf → S ∧ U whnf
  μ-whnf : ∀{A} → μ A whnf
  typdecl-whnf : ∀{K M} → [ typ M ∶ K ] whnf
  valdecl-whnf : ∀{ℓ A} → [ val ℓ ∶ A ] whnf

lift-preserves-whnf : ∀ f A → A whnf → liftType f A whnf
lift-preserves-whnf f ⊤ ⊤-whnf = ⊤-whnf
lift-preserves-whnf f ⊥ ⊥-whnf = ⊥-whnf
lift-preserves-whnf f [ typ M ∶ K ] typdecl-whnf = typdecl-whnf
lift-preserves-whnf f [ val ℓ ∶ A ] valdecl-whnf = valdecl-whnf
lift-preserves-whnf f (A ∧ B) (∧-whnf A-whnf B-whnf) =
  ∧-whnf (lift-preserves-whnf f A A-whnf) (lift-preserves-whnf f B B-whnf)
lift-preserves-whnf f (μ A) μ-whnf = μ-whnf
lift-preserves-whnf f (ℿ J K) ℿ-whnf = ℿ-whnf
lift-preserves-whnf f (ƛ x A) ƛ-whnf = ƛ-whnf

infix 4 _tyval _store

data _tyval : Kind → Set where
  intv-val : ∀ {α} → α whnf → α ∙∙ α tyval
  pi-val : ∀ {J K} → K inert-kd → ℿ J K tyval

-- TODO
data _store : Context → Set where
  empty-store : [] store
  cons-store-kd : ∀ {Γ x k} → Γ store → k tyval → Γ & x ~ Kd k store
  cons-store-ty : ∀ {Γ x τ} → Γ store → τ inert-ty → Γ & x ~ Ty τ store

denot : Context → Type → (K : Kind) → (s : KindShape) → Set
denot Γ τ (S ∙∙ U) _ = τ whnf × Γ ⊢#ty S ≤ τ ∈ ✶ × Γ ⊢#ty τ ≤ U ∈ ✶
denot Γ (ƛ J' A) (ℿ J K) (Pi sJ sK) =
    Γ ⊢#kd J ≤ J' ×
    (∀ τ x →
      denot Γ τ J sJ →
      Γ & x ~ Kd S[ τ ∈ J ] ⊢#ty openType x A ∈ openKind x K →
      Σ[ α ∈ Type ]
      ((Γ & x ~ Kd S[ τ ∈ J ]) ⊢#ty A == α ∈ openKind x K ×
        denot (Γ & x ~ Kd S[ τ ∈ J ]) α (openKind x K) sK))
denot Γ _ (ℿ J K) _ = Void

⟨_,_⟩∈'⟦_⟧ : Context → Type → Kind → Set
⟨ Γ , A ⟩∈'⟦ K ⟧ = denot Γ A K (kd-shape K)

denot-measure-inv : ∀{Γ A x K} →
  denot Γ A (openKind x K) (kd-shape K) ≡
  denot Γ A (openKind x K) (kd-shape (openKind x K))
denot-measure-inv {Γ} {A} {x} {K} =
  cong (denot Γ A (openKind x K)) (sym (liftKind-preserves-shape (openVar x) K))

denot-measure-open : ∀{Γ A x K} →
  denot Γ A (openKind x K) (kd-shape K) →
  denot Γ A (openKind x K) (kd-shape (openKind x K))
denot-measure-open {Γ} {A} {x} {K} p rewrite sym (denot-measure-inv {Γ} {A} {x} {K}) = p

denot-measure-close : ∀{Γ A x K} →
  denot Γ A (openKind x K) (kd-shape (openKind x K)) →
  denot Γ A (openKind x K) (kd-shape K)
denot-measure-close {Γ} {A} {x} {K} p rewrite (denot-measure-inv {Γ} {A} {x} {K}) = p

mutual
  data ⟨_,_⟩∈⟦_⟧ : Context → Type → Kind → Set where
    denot-intv : ∀{Γ τ S U} →
      τ whnf → Γ ⊢#ty S ≤ τ ∈ ✶ → Γ ⊢#ty τ ≤ U ∈ ✶ → ⟨ Γ , τ ⟩∈⟦ S ∙∙ U ⟧
    denot-pi : ∀{Γ J' A J K} →
      Γ ⊢#kd J ≤ J' →
      (∀ τ x →
        ⟨ Γ , τ ⟩∈'⟦ J ⟧ →
        Γ & x ~ Kd S[ τ ∈ J ] ⊢#ty openType x A ∈ openKind x K →
        ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧) →
      ⟨ Γ , ƛ J' A ⟩∈⟦ ℿ J K ⟧

  record ⟨_,_⟩∈ℰ⟦_⟧ (Γ : Context) (A : Type) (K : Kind) : Set where
    inductive
    constructor denot-eval
    field
      result : Type
      A==result : Γ ⊢#ty A == result ∈ K
      result∈⟦K⟧ : ⟨ Γ , result ⟩∈⟦ K ⟧

-- whyyyy does this have to be so _complicated_
denot-rec-ind-impl : ∀{Γ τ K} →
  (sK : KindShape) →
  (kd-shape K ≡ sK) →
  denot Γ τ K sK → ⟨ Γ , τ ⟩∈⟦ K ⟧
denot-rec-ind-impl {K = S ∙∙ U} _ _ (τ-whnf , S≤τ , τ≤U) = denot-intv τ-whnf S≤τ τ≤U
denot-rec-ind-impl {Γ} {ƛ J' A} {ℿ J K} (Pi sJ sK) eq (J≤J' , body-normalizes) =
  denot-pi J≤J' (body-normalizes' (proj₁ (unwrap-Pi-shape eq)))
  where
    body-normalizes' : kd-shape J ≡ sJ →
      ∀ τ x →
      ⟨ Γ , τ ⟩∈'⟦ J ⟧ →
      Γ & x ~ Kd S[ τ ∈ J ] ⊢#ty openType x A ∈ openKind x K →
      ⟨ Γ & x ~ Kd S[ τ ∈ J ] , A ⟩∈ℰ⟦ openKind x K ⟧
    body-normalizes' refl τ x ⟨Γ,τ⟩∈'⟦J⟧ Γx⊢#xA∈xK =
      let (α , Γx⊢#A==α , denot-Γx-α-xK-sK) = body-normalizes τ x ⟨Γ,τ⟩∈'⟦J⟧ Γx⊢#xA∈xK
       in
      denot-eval α Γx⊢#A==α (denot-rec-ind-impl sK shape-xK≡sK denot-Γx-α-xK-sK)
      where
        shape-xK≡shape-K : kd-shape (openKind x K) ≡ kd-shape K
        shape-xK≡shape-K = liftKind-preserves-shape (openVar x) K

        shape-K≡sK : kd-shape K ≡ sK
        shape-K≡sK = proj₂ (unwrap-Pi-shape eq)

        shape-xK≡sK : kd-shape (openKind x K) ≡ sK
        shape-xK≡sK = trans shape-xK≡shape-K shape-K≡sK

denot-ind-rec-impl : ∀{Γ τ K} →
  (sK : KindShape) →
  (kd-shape K ≡ sK) →
  ⟨ Γ , τ ⟩∈⟦ K ⟧ → denot Γ τ K sK
denot-ind-rec-impl {K = S ∙∙ U} _ _ (denot-intv τ-whnf S≤τ τ≤U) = (τ-whnf , S≤τ , τ≤U)
denot-ind-rec-impl {Γ} {ƛ J' A} {ℿ J K} (Pi sJ sK) eq (denot-pi J≤J' body-normalizes') =
  (J≤J' , body-normalizes (proj₁ (unwrap-Pi-shape eq)))
  where
    body-normalizes : kd-shape J ≡ sJ →
      ∀ τ x →
      denot Γ τ J sJ →
      Γ & x ~ Kd S[ τ ∈ J ] ⊢#ty openType x A ∈ openKind x K →
      Σ[ α ∈ Type ]
      ((Γ & x ~ Kd S[ τ ∈ J ]) ⊢#ty A == α ∈ openKind x K ×
        denot (Γ & x ~ Kd S[ τ ∈ J ]) α (openKind x K) sK)
    body-normalizes refl τ x ⟨Γ,τ⟩∈'⟦J⟧ Γx⊢#xA∈xK =
      let (denot-eval α Γx⊢#A==α ⟨Γx,α⟩∈⟦xK⟧) = body-normalizes' τ x ⟨Γ,τ⟩∈'⟦J⟧ Γx⊢#xA∈xK
      in
        (α , Γx⊢#A==α , denot-ind-rec-impl sK shape-xK≡sK ⟨Γx,α⟩∈⟦xK⟧)
      where
        shape-xK≡shape-K : kd-shape (openKind x K) ≡ kd-shape K
        shape-xK≡shape-K = liftKind-preserves-shape (openVar x) K

        shape-K≡sK : kd-shape K ≡ sK
        shape-K≡sK = proj₂ (unwrap-Pi-shape eq)

        shape-xK≡sK : kd-shape (openKind x K) ≡ sK
        shape-xK≡sK = trans shape-xK≡shape-K shape-K≡sK

denot-rec-ind : ∀{Γ τ K} → ⟨ Γ , τ ⟩∈'⟦ K ⟧ → ⟨ Γ , τ ⟩∈⟦ K ⟧
denot-rec-ind {K = K} = denot-rec-ind-impl (kd-shape K) refl

denot-ind-rec : ∀{Γ τ K} → ⟨ Γ , τ ⟩∈⟦ K ⟧ → ⟨ Γ , τ ⟩∈'⟦ K ⟧
denot-ind-rec {K = K} = denot-ind-rec-impl (kd-shape K) refl

weak-head-normalization : ∀ {Γ A K} →
  Γ store →
  Γ ⊢#ty A ∈ K →
  ⟨ Γ , A ⟩∈ℰ⟦ K ⟧
weak-head-normalization Γ-store (k-var-# Γ-ctx Γ[x]⊢>K) = {! !}
weak-head-normalization Γ-store k-top-# =
  denot-eval ⊤ (==-refl-# k-top-#)
    (denot-intv ⊤-whnf (st-top-# k-bot-#) (st-refl-# k-top-#))
weak-head-normalization Γ-store k-bot-# =
  denot-eval ⊥ (==-refl-# k-bot-#)
    (denot-intv ⊥-whnf (st-refl-# k-bot-#) (st-top-# k-bot-#))
weak-head-normalization {Γ} {A} Γ-store (k-sing-# Γ⊢#A∈S∙∙U) =
  denot-eval τ (eq-narrow-# A==τ∈S∙∙U) (denot-intv τ-whnf A≤τ τ≤A)
  where
    ⟨Γ,A⟩∈ℰ⟦S∙∙U⟧ = weak-head-normalization Γ-store Γ⊢#A∈S∙∙U

    unwrap-denot : ∀{Γ τ S U} → ⟨ Γ , τ ⟩∈⟦ S ∙∙ U ⟧ → τ whnf
    unwrap-denot (denot-intv τ-whnf _ _) = τ-whnf

    open ⟨_,_⟩∈ℰ⟦_⟧
    τ = result ⟨Γ,A⟩∈ℰ⟦S∙∙U⟧
    A==τ∈S∙∙U = A==result ⟨Γ,A⟩∈ℰ⟦S∙∙U⟧
    τ∈⟦S∙∙U⟧ = result∈⟦K⟧ ⟨Γ,A⟩∈ℰ⟦S∙∙U⟧

    τ-whnf : τ whnf
    τ-whnf = unwrap-denot τ∈⟦S∙∙U⟧

    A==τ∈✶ : Γ ⊢#ty A == τ ∈ ✶
    A==τ∈✶ = proper-types-equality-# A==τ∈S∙∙U

    A≤τ = eq-left-# A==τ∈✶
    τ≤A = eq-right-# A==τ∈✶
weak-head-normalization {A = ℿ S T} Γ-store Γ⊢#ℿST∈✶@(k-arr-# Γ⊢#S∈✶ Γx⊢#xT∈✶) =
  denot-eval (ℿ S T) (eq-refl-# Γ⊢#ℿST∈✶)
    (denot-intv ℿ-whnf (st-bot-# Γ⊢#ℿST∈✶) (st-top-# Γ⊢#ℿST∈✶))
weak-head-normalization Γ-store (k-abs-# {x} Γ⊢#J-kd Γx∶J⊢xA∈xK) = {!!}
weak-head-normalization Γ-store (k-app-# Γ⊢#F∈ℿJK Γ⊢#A∈J) =
  let denot-eval f F==f f∈⟦ℿJK⟧ = weak-head-normalization Γ-store Γ⊢#F∈ℿJK
      denot-eval α A==α α∈⟦J⟧ = weak-head-normalization Γ-store Γ⊢#A∈J
   in
  {!!}
weak-head-normalization Γ-store (k-intersect-# Γ⊢#S∈✶ Γ⊢#U∈✶) = {! !}
weak-head-normalization Γ-store (k-sub-# Γ⊢#A∈J J≤K) = {! !}
weak-head-normalization Γ-store (k-field-# Γ⊢#A∈K) = {! !}
weak-head-normalization Γ-store (k-typ-# x) = {! !}
weak-head-normalization Γ-store (k-sel-# x) = {! !}
weak-head-normalization Γ-store (k-rec-# x) = {! !}
