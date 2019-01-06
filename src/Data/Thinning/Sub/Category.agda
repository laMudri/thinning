module Data.Thinning.Sub.Category where

  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Function using (_on_)
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  open import Egads.Category
  open import Egads.Prelude hiding (_≤_) renaming (zero to lzero; suc to lsuc)

  open import Data.Thinning
  open import Data.Thinning.Sub

  SUBTHIN : ℕ → Category lzero lzero lzero
  SUBTHIN n = record
    { Obj = ∃ λ m → m ≤ n
    ; categoryOverObjs = record
      { Hom = λ where (_ , θ) (_ , φ) → ≡.setoid (θ ⊆ φ)
      ; categoryOverHoms = record
        { id = const oii
        ; comp = λ where
          ._⟨$⟩_ (sub , sub′) → sub ⊆->> sub′
          .cong (≡.refl , ≡.refl) → ≡.refl
        ; isCategory = record
          { identity = oii->> , >>-oii
          ; assoc = ⊆->>->>
          }
        }
      }
    }
