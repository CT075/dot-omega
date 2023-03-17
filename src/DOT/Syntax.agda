open import Level renaming (zero to lzero; suc to lsuc) hiding (Lift)
open import Relation.Binary using (DecSetoid)

module DOT.Syntax {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import Data.Fin using (Fin; suc; zero)
open import Data.Nat using (ℕ; suc; zero)
open import Data.List using (List; []; _∷_)

open import Data.Var using (Var; Lift)

TypeLabel = DecSetoid.Carrier TypeL
TermLabel = DecSetoid.Carrier TermL

mutual
  data Type : Set where
    ⊤ : Type                               -- top
    ⊥ : Type                               -- bottom
    [_] : Decl → Type                      -- record
    _∧_ : Type → Type → Type               -- intersection
    _∙_ : Var → TypeLabel → Type           -- type selection
    μ : Type → Type                        -- recursive types
    ℿ : Type → Type → Type                 -- dependent function

  data Decl : Set where
    [_∶_∙∙_] : TypeLabel → Type → Type → Decl
    [_∶_] : TermLabel → Type → Decl

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

mutual
  liftType : (Var → Var) → Type → Type
  liftType f ⊤ = ⊤
  liftType f ⊥ = ⊥
  liftType f [ decl ] = [ liftDecl f decl ]
  liftType f (τ₁ ∧ τ₂) = liftType f τ₁ ∧ liftType f τ₂
  liftType f (x ∙ ℓ) = f x ∙ ℓ
  liftType f (μ τ) = μ (liftType f τ)
  liftType f (ℿ τ ρ) = ℿ (liftType f τ) (liftType f ρ)

  liftDecl : (Var → Var) → Decl → Decl
  liftDecl f [ ℓ ∶ τ₁ ∙∙ τ₂ ] = [ ℓ ∶ liftType f τ₁ ∙∙ liftType f τ₂ ]
  liftDecl f [ ℓ ∶ τ ] = [ ℓ ∶ liftType f τ ]

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
  liftDefn f (typ ℓ =' τ) = typ ℓ =' (liftType f τ)
  liftDefn f (val ℓ =' e) = val ℓ =' (liftTerm f e)

open Lift (record {lift = liftTerm}) renaming
  ( openT to openTerm
  ; closeT to closeTerm
  ; wkT to wkTerm
  ; shiftT to shiftTerm
  ; renameT to renameTerm
  )
  public

open Lift (record {lift = liftType}) renaming
  ( openT to openType
  ; closeT to closeType
  ; wkT to wkType
  ; shiftT to shiftType
  ; renameT to renameType
  )
  public
