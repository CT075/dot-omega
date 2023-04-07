open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOTOmega.Typing.GeneralToTight {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Context

open import DOTOmega.Syntax TypeL TermL
open import DOTOmega.Typing TypeL TermL
open import DOTOmega.Typing.Tight TypeL TermL

st-β-premise : ∀ {Γ A B J K x} →
  Γ inert-ctx →
  Γ ⊢#ty B ∈ J →
  Γ & x ~ Kd J ⊢#ty openType x A ∈ K →
  Γ & x ~ Kd (S[ A ∈ J ]) ⊢#ty openType x A ∈ K
st-β-premise Γinert B∈J A∈K = {!!}

⊢→⊢#-st : ∀ {Γ S U k} → Γ inert-ctx → Γ ⊢ty S ≤ U ∈ k → Γ ⊢#ty S ≤ U ∈ k
⊢→⊢#-st = {!!}

⊢→⊢#-tm : ∀ {Γ e τ} → Γ inert-ctx → Γ ⊢tm e ∈ τ → Γ ⊢#tm e ∈ τ
⊢→⊢#-tm = {!!}
