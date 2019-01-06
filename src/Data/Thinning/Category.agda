module Data.Thinning.Category where

  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  open import Egads.Category
  open import Egads.Prelude hiding (_≤_) renaming (zero to lzero; suc to lsuc)

  open import Data.Thinning

  THIN : Category lzero lzero lzero
  THIN = record
    { Obj = ℕ
    ; categoryOverObjs = record
      { Hom = λ m n → ≡.setoid (m ≤ n)
      ; categoryOverHoms = record
        { id = const oi
        ; comp = λ where
          ._⟨$⟩_ (θ , φ) → θ >> φ
          .cong (≡.refl , ≡.refl) → ≡.refl
        ; isCategory = record
          { identity = oi->> , >>-oi
          ; assoc = >>->>
          }
        }
      }
    }
