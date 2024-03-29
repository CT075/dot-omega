open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.Inertness
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.All using (All)
open import Relation.Nullary.Negation using (¬_)

open import Data.Var
open import Data.Context

open import DOTOmega.Syntax TypeL TermL hiding (_∉_; _∈_)
open import DOTOmega.Typing TypeL TermL

-- Higher-kinded singletons

S[_∈_] : Type → Kind → Kind
S[ τ ∈ A ∙∙ B ] = τ ∙∙ τ
S[ f ∈ ℿ J K ] = ℿ J (S[ wkType f ⊡ `(Bound zero) ∈ K ])

-- Definition and properties of inert contexts

infix 4 _inert-kd _inert-ty _inert-ctx _recd _is-recd-label

label-of-decl : Decl → Label
label-of-decl (val ℓ ∶ τ) = TmL ℓ
label-of-decl (typ M ∶ K) = TyL M

data _≈_ : Label → Label → Set where
  Tm= : ∀{ℓ₁ ℓ₂} → ℓ₁ ≈Tm ℓ₂ → TmL ℓ₁ ≈ TmL ℓ₂
  Ty= : ∀{M₁ M₂} → M₁ ≈Ty M₂ → TyL M₁ ≈ TyL M₂

_∈_ : Label → List Label → Set
ℓ ∈ ℓs = Any (ℓ ≈_) ℓs

_∉_ : Label → List Label → Set
ℓ ∉ ℓs = ¬ (ℓ ∈ ℓs)

disjoint : List Label → List Label → Set
disjoint xs ys = All (_∉ ys) xs

data _is-recd-label : Decl → Set where
  val-is-recd : ∀ {ℓ τ} → val ℓ ∶ τ is-recd-label
  ty-is-recd : ∀ {M τ K} → typ M ∶ S[ τ ∈ K ] is-recd-label

data RecordLabels : Type → List Label → Set where
  labels-single : ∀ {D} →
    D is-recd-label →
    RecordLabels [ D ] (label-of-decl D ∷ [])
  labels-join : ∀ {S U ℓs₁ ℓs₂} →
    RecordLabels S ℓs₁ →
    RecordLabels U ℓs₂ →
    disjoint ℓs₁ ℓs₂ →
    RecordLabels (S ∧ U) (ℓs₁ ++ ℓs₂)

_recd : Type → Set
τ recd = Σ[ ℓs ∈ List Label ] (RecordLabels τ ℓs)

data _inert-kd : Kind → Set where
  intv-inert : ∀ {A} → A ∙∙ A inert-kd
  pi-inert : ∀ {J K} → K inert-kd → ℿ J K inert-kd

data _inert-ty : Type → Set where
  ℿ-inert : ∀ {τ₁ τ₂} → ℿ τ₁ τ₂ inert-ty
  μ-inert : ∀ {τ} →
    -- TODO: Do we just not allow nested recursive types?
    τ recd →
    μ τ inert-ty

data _inert-ctx : Context → Set where
  empty-inert : [] inert-ctx
  cons-inert-ty : ∀ {Γ x τ} → Γ inert-ctx → τ inert-ty → Γ & x ~ Ty τ inert-ctx
  cons-inert-kd : ∀ {Γ x k} → Γ inert-ctx → k inert-kd → Γ & x ~ Kd k inert-ctx
