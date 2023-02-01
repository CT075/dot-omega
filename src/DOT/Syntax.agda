open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary using (DecSetoid)

module DOT.Syntax {ℓ}
    (TypeL : DecSetoid lzero ℓ)
    (TermL : DecSetoid lzero ℓ)
  where

open import DOT.Syntax.Base TypeL TermL public
open import DOT.Syntax.Context TypeL TermL public
