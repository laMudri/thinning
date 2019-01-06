module Data.Thinning where

  open import Data.Empty
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Data.Nat.Properties using (+-suc)
  open import Relation.Binary.PropositionalEquality

  infix 4 _≤_ _<_
  infixr 5 _>>_

  -- Order-preserving embeddings: a list of keep/drop (os/o′) instructions
  -- terminated by oz
  -- m ≤ n: n is the number of elements originally
  --        m is the number of elements kept
  data _≤_ : ℕ → ℕ → Set where
    oz :                    zero ≤ zero
    os : ∀ {m n} → m ≤ n → suc m ≤ suc n
    o′ : ∀ {m n} → m ≤ n →     m ≤ suc n

  -- The empty thinning: drop everything
  oe : ∀ {n} → 0 ≤ n
  oe {zero} = oz
  oe {suc n} = o′ oe

  -- The identity thinning: keep everything
  oi : ∀ {n} → n ≤ n
  oi {zero} = oz
  oi {suc n} = os oi

  -- Make an embedding smaller by removing the first keep
  op : ∀ {m n} → suc m ≤ suc n → m ≤ n
  op (os θ) = θ
  op {n = zero} (o′ ())
  op {n = suc n} (o′ θ) = o′ (op θ)

  -- Keeping at least one element
  _<_ : (m n : ℕ) → Set
  m < n = suc m ≤ n

  k+<⇒≱ : ∀ {m n} k → k + m < n → n ≤ m → ⊥
  k+<⇒≱ k () oz
  k+<⇒≱ {suc m} {suc n} k θ (os φ) rewrite +-suc k m = k+<⇒≱ k (op θ) φ
  k+<⇒≱ {suc m} {n} k θ (o′ φ) rewrite +-suc k m = k+<⇒≱ (suc k) θ φ

  -- The main way of proving that an embedding is impossible:
  -- giving an embedding that contradicts it
  <⇒≱ : ∀ {m n} → m < n → n ≤ m → ⊥
  <⇒≱ = k+<⇒≱ 0

  oe-unique : ∀ {n} (θ φ : 0 ≤ n) → θ ≡ φ
  oe-unique oz oz = refl
  oe-unique (o′ θ) (o′ φ) = cong o′ (oe-unique θ φ)

  oi-unique : ∀ {n} (θ φ : n ≤ n) → θ ≡ φ
  oi-unique θ (o′ φ) = ⊥-elim (<⇒≱ oi φ)
  oi-unique (o′ θ) (os φ) = ⊥-elim (<⇒≱ oi θ)
  oi-unique oz oz = refl
  oi-unique (os θ) (os φ) = cong os (oi-unique θ φ)

  -- Composition of thinnings:
  -- an element is kept iff it is kept by both thinnings
  _>>_ : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
  θ >> oz = θ
  os θ >> os φ = os (θ >> φ)
  o′ θ >> os φ = o′ (θ >> φ)
  θ >> o′ φ = o′ (θ >> φ)

  -- Category laws
  oi->> : ∀ {n o} (φ : n ≤ o) → oi >> φ ≡ φ
  oi->> oz = refl
  oi->> (os φ) = cong os (oi->> φ)
  oi->> (o′ φ) = cong o′ (oi->> φ)

  >>-oi : ∀ {m n} (θ : m ≤ n) → θ >> oi ≡ θ
  >>-oi oz = refl
  >>-oi (os θ) = cong os (>>-oi θ)
  >>-oi (o′ θ) = cong o′ (>>-oi θ)

  >>->> : ∀ {m n o p} (θ : m ≤ n) (φ : n ≤ o) (χ : o ≤ p) →
          (θ >> φ) >> χ ≡ θ >> (φ >> χ)
  >>->> θ φ oz = refl
  >>->> θ φ (o′ χ) = cong o′ (>>->> θ φ χ)
  >>->> θ (o′ φ) (os χ) = cong o′ (>>->> θ φ χ)
  >>->> (os θ) (os φ) (os χ) = cong os (>>->> θ φ χ)
  >>->> (o′ θ) (os φ) (os χ) = cong o′ (>>->> θ φ χ)
