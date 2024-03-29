open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

-- TODO: We basically never actually use the Setoid structure of labels
-- anywhere (we can use [PropositionalEquality] basically everywhere).
module DOTOmega.Syntax
    (TypeL : DecSetoid lzero lzero)
    (TermL : DecSetoid lzero lzero)
  where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded
open import Function.Base using (id)

open import Data.Var using (Var; Lift; Subst; openVar)
open import Induction.Extensions

TypeLabel = DecSetoid.Carrier TypeL
TermLabel = DecSetoid.Carrier TermL
_≈Ty_ = DecSetoid._≈_ TypeL
_≈Tm_ = DecSetoid._≈_ TermL

infix 19 typ_∶_
infix 20 _∙∙_
infix 21 _∧_

-- Core syntax

mutual
  data Kind : Set where
    _∙∙_ : Type → Type → Kind              -- interval kinds
    ℿ : Kind → Kind → Kind                 -- type-level function kinds

  data Type : Set where
    ⊤ : Type                               -- top
    ⊥ : Type                               -- bottom
    [_] : Decl → Type                      -- record
    _∧_ : Type → Type → Type               -- intersection
    _∙_ : Var → TypeLabel → Type           -- type selection
    μ : Type → Type                        -- recursive types
    ℿ : Type → Type → Type                 -- dependent function
    ƛ : Kind → Type → Type                 -- type lambda
    ` : Var → Type                         -- type variable
    _⊡_ : Type → Type → Type               -- application

  data Decl : Set where
    typ_∶_ : TypeLabel → Kind → Decl
    val_∶_ : TermLabel → Type → Decl

pattern ✶ = ⊥ ∙∙ ⊤

mutual
  data Term : Set where
    ` : Var → Term                         -- variables
    V : Val → Term                         -- values
    _∙_ : Var → TermLabel → Term           -- field selection
    _⊡_ : Var → Var → Term                 -- application
    let'_in'_ : Term → Term → Term         -- let-binding

  data Val : Set where
    new : Type → List Defn → Val           -- new object definitions
    ƛ : Type → Term → Val                  -- lambdas

  data Defn : Set where
    typ_='_ : TypeLabel → Type → Defn
    val_='_ : TermLabel → Term → Defn

-- Utility functions

data Label : Set where
  TyL : TypeLabel → Label
  TmL : TermLabel → Label

data defnMatchesType : TypeLabel → Defn → Set where
  dmty-lbl : ∀{A A' τ} → A ≈Ty A' → defnMatchesType A' (typ A =' τ)

data defnMatchesTerm : TermLabel → Defn → Set where
  dmtm-lbl : ∀{ℓ ℓ' e} → ℓ ≈Tm ℓ' → defnMatchesTerm ℓ' (val ℓ =' e)

_∈_ : Defn → List Defn → Set
(typ A =' _) ∈ ds = Any (defnMatchesType A) ds
(val ℓ =' _) ∈ ds = Any (defnMatchesTerm ℓ) ds

_∉_ : Defn → List Defn → Set
d ∉ ds = ¬ (d ∈ ds)

-- Locally-nameless operations

mutual
  liftKind : (Var → Var) → Kind → Kind
  liftKind f (τ₁ ∙∙ τ₂) = liftType f τ₁ ∙∙ liftType f τ₂
  liftKind f (ℿ J K) = ℿ (liftKind f J) (liftKind f K)

  liftType : (Var → Var) → Type → Type
  liftType f ⊤ = ⊤
  liftType f ⊥ = ⊥
  liftType f [ decl ] = [ liftDecl f decl ]
  liftType f (τ₁ ∧ τ₂) = liftType f τ₁ ∧ liftType f τ₂
  liftType f (x ∙ A) = f x ∙ A
  liftType f (μ τ) = μ (liftType f τ)
  liftType f (ℿ τ ρ) = ℿ (liftType f τ) (liftType f ρ)
  liftType f (ƛ k τ) = ƛ (liftKind f k) (liftType f τ)
  liftType f (` x) = ` (f x)
  liftType f (g ⊡ τ) = liftType f g ⊡ liftType f τ

  liftDecl : (Var → Var) → Decl → Decl
  liftDecl f (typ A ∶ k) = typ A ∶ liftKind f k
  liftDecl f (val ℓ ∶ τ) = val ℓ ∶ liftType f τ

  liftTerm : (Var → Var) → Term → Term
  liftTerm f (` x) = ` (f x)
  liftTerm f (V vl) = V (liftVal f vl)
  liftTerm f (a ∙ b) = f a ∙ b
  liftTerm f (a ⊡ b) = f a ⊡ f b
  liftTerm f (let' t1 in' t2) = let' (liftTerm f t1) in' (liftTerm f t2)

  liftVal : (Var → Var) → Val → Val
  liftVal f (ƛ τ e) = ƛ τ (liftTerm f e)
  liftVal f (new τ defns) = new (liftType f τ) (mapf defns)
    where
      mapf : List Defn → List Defn
      mapf [] = []
      mapf (defn ∷ defns) = liftDefn f defn ∷ mapf defns

  liftDefn : (Var → Var) → Defn → Defn
  liftDefn f (typ A =' τ) = typ A =' (liftType f τ)
  liftDefn f (val ℓ =' e) = val ℓ =' (liftTerm f e)

instance
  KindLift : Lift Kind
  KindLift = record {lift = liftKind}

  TermLift : Lift Term
  TermLift = record {lift = liftTerm}

  ValLift : Lift Val
  ValLift = record {lift = liftVal}

  TypeLift : Lift Type
  TypeLift = record {lift = liftType}

  DefnLift : Lift Defn
  DefnLift = record {lift = liftDefn}

mutual
  _/Kind_ : (Var → Type) → Kind → Kind
  _/Kind_ f (A ∙∙ B) = _/Type_ f A ∙∙ _/Type_ f B
  _/Kind_ f (ℿ J K) = ℿ (_/Kind_ f J) (_/Kind_ f K)

  _/Type_ : (Var → Type) → Type → Type
  _/Type_ f ⊤ = ⊤
  _/Type_ f ⊥ = ⊥
  _/Type_ f [ decl ] = [ _/Decl_ f decl ]
  _/Type_ f (τ₁ ∧ τ₂) = _/Type_ f τ₁ ∧ _/Type_ f τ₂
  _/Type_ f (x ∙ A) = x ∙ A
  _/Type_ f (μ τ) = μ (_/Type_ f τ)
  _/Type_ f (ℿ τ ρ) = ℿ (_/Type_ f τ) (_/Type_ f ρ)
  _/Type_ f (ƛ k τ) = ƛ (_/Kind_ f k) (_/Type_ f τ)
  _/Type_ f (` x) = f x
  _/Type_ f (g ⊡ τ) = _/Type_ f g ⊡ _/Type_ f τ

  _/Decl_ : (Var → Type) → Decl → Decl
  _/Decl_ f (typ A ∶ k) = typ A ∶ _/Kind_ f k
  _/Decl_ f (val ℓ ∶ τ) = val ℓ ∶ _/Type_ f τ

  _/Term_ : (Var → Type) → Term → Term
  _/Term_ f (` x) = ` x
  _/Term_ f (V vl) = V (_/Val_ f vl)
  _/Term_ f (a ∙ b) = a ∙ b
  _/Term_ f (a ⊡ b) = a ⊡ b
  _/Term_ f (let' t1 in' t2) = let' (_/Term_ f t1) in' (_/Term_ f t2)

  _/Val_ : (Var → Type) → Val → Val
  _/Val_ f (ƛ τ e) = ƛ τ (_/Term_ f e)
  _/Val_ f (new τ defns) = new (_/Type_ f τ) (mapf defns)
    where
      mapf : List Defn → List Defn
      mapf [] = []
      mapf (defn ∷ defns) = _/Defn_ f defn ∷ mapf defns

  _/Defn_ : (Var → Type) → Defn → Defn
  _/Defn_ f (typ A =' τ) = typ A =' (_/Type_ f τ)
  _/Defn_ f (val ℓ =' e) = val ℓ =' (_/Term_ f e)

open Subst (record {lift = KindLift; var = `; subst = _/Kind_})
  using ()
  renaming
  ( openT to openKind
  ; closeT to closeKind
  ; wkT to wkKind
  ; shiftT to shiftKind
  ; renameT to renameKind
  ; bindT to bindKind
  )
  public

open Subst (record {lift = TermLift; var = `; subst = _/Term_})
  using ()
  renaming
  ( openT to openTerm
  ; closeT to closeTerm
  ; wkT to wkTerm
  ; shiftT to shiftTerm
  ; renameT to renameTerm
  ; bindT to bindTerm
  )
  public

open Subst (record {lift = TypeLift; var = `; subst = _/Type_})
  using ()
  renaming
  ( openT to openType
  ; closeT to closeType
  ; wkT to wkType
  ; shiftT to shiftType
  ; renameT to renameType
  ; bindT to bindType
  )
  public

open Subst (record {lift = DefnLift; var = `; subst = _/Defn_})
  using ()
  renaming
  ( openT to openDefn
  ; closeT to closeDefn
  ; wkT to wkDefn
  ; shiftT to shiftDefn
  ; renameT to renameDefn
  ; bindT to bindDefn
  )
  public

open Subst (record {lift = KindLift; var = id; subst = liftKind})
  using ()
  renaming (bindT to plugKind)
  public

open Subst (record {lift = TypeLift; var = id; subst = liftType})
  using ()
  renaming (bindT to plugType)
  public

open Subst (record {lift = DefnLift; var = id; subst = liftDefn})
  using ()
  renaming (bindT to plugDefn)
  public

open Subst (record {lift = TermLift; var = id; subst = liftTerm})
  using ()
  renaming (bindT to plugTerm)
  public

data KindShape : Set where
  Interval : KindShape
  Pi : KindShape → KindShape → KindShape

kd-shape : Kind → KindShape
kd-shape (S ∙∙ U) = Interval
kd-shape (ℿ J K) = Pi (kd-shape J) (kd-shape K)

liftKind-preserves-shape : ∀ (f : Var → Var) K →
  kd-shape (liftKind f K) ≡ kd-shape K
liftKind-preserves-shape f (S ∙∙ U) = refl
liftKind-preserves-shape f (ℿ J K) = begin
    kd-shape (liftKind f (ℿ J K))
  ≡⟨ refl ⟩
    kd-shape (ℿ (liftKind f J) (liftKind f K))
  ≡⟨ refl ⟩
    Pi (kd-shape (liftKind f J)) (kd-shape (liftKind f K))
  ≡⟨ cong
      (λ t → Pi t (kd-shape (liftKind f K)))
      (liftKind-preserves-shape f J) ⟩
    Pi (kd-shape J) (kd-shape (liftKind f K))
  ≡⟨ cong (Pi (kd-shape J)) (liftKind-preserves-shape f K) ⟩
    Pi (kd-shape J) (kd-shape K)
  ≡⟨ refl ⟩
    kd-shape (ℿ J K)
  ∎
  where
    open ≡-Reasoning

unwrap-Pi-shape : ∀ {J K sJ sK} → kd-shape (ℿ J K) ≡ Pi sJ sK →
  kd-shape J ≡ sJ × kd-shape K ≡ sK
unwrap-Pi-shape {J} {K} {sJ} {sK} eq = split sJ sK (kd-shape J) (kd-shape K) eq
  where
    split : ∀ sJ sK sJ' sK' → Pi sJ' sK' ≡ Pi sJ sK → sJ' ≡ sJ × sK' ≡ sK
    split sJ sK .sJ .sK refl = refl , refl

infix 19 _<kd_

-- TODO: is this still true?
-- This measure is primarily used for the logical relation for type-level
-- normalization, which doesn't need to recurse into the type expressions
-- themselves. Because of that, we can just count [S ∙∙ U] as the base.
kd-size : Kind → ℕ
kd-size (S ∙∙ U) = 1
kd-size (ℿ J K) = suc (kd-size J + kd-size K)

_<kd_ : Kind → Kind → Set
J <kd K = kd-size J < kd-size K

<kd-wf : ∀ K → Acc _<kd_ K
<kd-wf = accMeasure kd-size

<kd-ℿ₁ : ∀ J K → J <kd ℿ J K
<kd-ℿ₁ J K = s≤s (m≤m+n (kd-size J) (kd-size K))

<kd-ℿ₂ : ∀ J K → K <kd ℿ J K
<kd-ℿ₂ J K = s≤s (m≤n+m (kd-size K) (kd-size J))

liftKind-preserves-size : ∀ (f : Var → Var) K →
  kd-size (liftKind f K) ≡ kd-size K
liftKind-preserves-size f (A ∙∙ B) = refl
liftKind-preserves-size f (ℿ J K) = begin
    kd-size (liftKind f (ℿ J K))
  ≡⟨ refl ⟩
    kd-size (ℿ (liftKind f J) (liftKind f K))
  ≡⟨ refl ⟩
    suc (kd-size (liftKind f J) + kd-size (liftKind f K))
  ≡⟨ cong
      (λ t → suc (t + kd-size (liftKind f K)))
      (liftKind-preserves-size f J)
   ⟩
    suc (kd-size J + kd-size (liftKind f K))
  ≡⟨ cong
      (λ t → suc (kd-size J + t))
      (liftKind-preserves-size f K)
   ⟩
    suc (kd-size J + kd-size K)
  ≡⟨ refl ⟩
    kd-size (ℿ J K)
  ∎
  where
    open ≡-Reasoning

liftKind-preserves-<₁ : ∀ J K (f : Var → Var) →
  J <kd K → liftKind f J <kd K
liftKind-preserves-<₁ J K f J<K rewrite liftKind-preserves-size f J = J<K

<kd-ℿ-open : ∀ x J K → openKind x K <kd ℿ J K
<kd-ℿ-open x J K = liftKind-preserves-<₁ K (ℿ J K) (openVar x) (<kd-ℿ₂ J K)
