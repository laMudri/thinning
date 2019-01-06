module Data.Thinning.Sub where

  open import Data.Empty
  open import Data.Nat using (ℕ; zero; suc; _+_)
  open import Relation.Binary.PropositionalEquality

  open import Data.Thinning

  infix 4 _⊆_
  infixr 5 _⊆->>_

  -- Sub-thinnings
  -- A thinning θ : m ≤ n describes a set of size m made up of elements from n.
  -- θ ⊆ φ iff φ keeps at least the elements from n that θ does.
  data _⊆_ : ∀ {m m′ n} → m ≤ n → m′ ≤ n → Set where
    ozz :                                                 oz ⊆ oz
    oss : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → os θ ⊆ os φ
    o′s : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → o′ θ ⊆ os φ
    o′′ : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → o′ θ ⊆ o′ φ

  -- oe represents the empty set
  oee : ∀ {m n} {θ : m ≤ n} → oe ⊆ θ
  oee {θ = oz} = ozz
  oee {θ = os θ} = o′s oee
  oee {θ = o′ θ} = o′′ oee

  oii : ∀ {m n} {θ : m ≤ n} → θ ⊆ θ
  oii {θ = oz} = ozz
  oii {θ = os θ} = oss oii
  oii {θ = o′ θ} = o′′ oii

  -- oi represents the universal set
  oei : ∀ {m n} {θ : m ≤ n} → θ ⊆ oi
  oei {θ = oz} = ozz
  oei {θ = os θ} = oss oei
  oei {θ = o′ θ} = o′s oei

  -- A subset has size smaller than its superset.
  -- The elements of θ are taken from φ (and some are dropped, too).
  -- Useful for proving impossibility of sub-thinnings; combine with <⇒≱
  ⊆⇒≤ : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} → θ ⊆ φ → m ≤ m′
  ⊆⇒≤ ozz = oz
  ⊆⇒≤ (oss sub) = os (⊆⇒≤ sub)
  ⊆⇒≤ (o′s sub) = o′ (⊆⇒≤ sub)
  ⊆⇒≤ (o′′ sub) = ⊆⇒≤ sub

  _⊆->>_ : ∀ {m m′ m″ n} {θ : m ≤ n} {φ : m′ ≤ n} {χ : m″ ≤ n} →
           θ ⊆ φ → φ ⊆ χ → θ ⊆ χ
  sub ⊆->> ozz = sub
  oss sub ⊆->> oss sub′ = oss (sub ⊆->> sub′)
  o′s sub ⊆->> oss sub′ = o′s (sub ⊆->> sub′)
  o′′ sub ⊆->> o′s sub′ = o′s (sub ⊆->> sub′)
  o′′ sub ⊆->> o′′ sub′ = o′′ (sub ⊆->> sub′)

  oii->> : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} (sub : θ ⊆ φ) →
           oii ⊆->> sub ≡ sub
  oii->> ozz = refl
  oii->> (oss sub) = cong oss (oii->> sub)
  oii->> (o′s sub) = cong o′s (oii->> sub)
  oii->> (o′′ sub) = cong o′′ (oii->> sub)

  >>-oii : ∀ {m m′ n} {θ : m ≤ n} {φ : m′ ≤ n} (sub : θ ⊆ φ) →
           sub ⊆->> oii ≡ sub
  >>-oii ozz = refl
  >>-oii (oss sub) = cong oss (>>-oii sub)
  >>-oii (o′s sub) = cong o′s (>>-oii sub)
  >>-oii (o′′ sub) = cong o′′ (>>-oii sub)

  ⊆->>->> : ∀ {m m′ m″ m‴ n} {θ : m ≤ n} {φ : m′ ≤ n} {χ : m″ ≤ n} {ψ : m‴ ≤ n}
            (sub : θ ⊆ φ) (sub′ : φ ⊆ χ) (sub″ : χ ⊆ ψ) →
            (sub ⊆->> sub′) ⊆->> sub″ ≡ sub ⊆->> (sub′ ⊆->> sub″)
  ⊆->>->> sub sub′ ozz = refl
  ⊆->>->> (oss sub) (oss sub′) (oss sub″) = cong oss (⊆->>->> sub sub′ sub″)
  ⊆->>->> (o′s sub) (oss sub′) (oss sub″) = cong o′s (⊆->>->> sub sub′ sub″)
  ⊆->>->> (o′′ sub) (o′s sub′) (oss sub″) = cong o′s (⊆->>->> sub sub′ sub″)
  ⊆->>->> (o′′ sub) (o′′ sub′) (o′s sub″) = cong o′s (⊆->>->> sub sub′ sub″)
  ⊆->>->> (o′′ sub) (o′′ sub′) (o′′ sub″) = cong o′′ (⊆->>->> sub sub′ sub″)

  oee-unique : ∀ {m n} {θ : m ≤ n} (sub sub′ : oe ⊆ θ) → sub ≡ sub′
  oee-unique ozz ozz = refl
  oee-unique (o′s sub) (o′s sub′) = cong o′s (oee-unique sub sub′)
  oee-unique (o′′ sub) (o′′ sub′) = cong o′′ (oee-unique sub sub′)

  oii-unique : ∀ {m n} {θ : m ≤ n} (sub sub′ : θ ⊆ θ) → sub ≡ sub′
  oii-unique ozz ozz = refl
  oii-unique (oss sub) (oss sub′) = cong oss (oii-unique sub sub′)
  oii-unique (o′′ sub) (o′′ sub′) = cong o′′ (oii-unique sub sub′)

  oei-unique : ∀ {m n} {θ : m ≤ n} (sub sub′ : θ ⊆ oi) → sub ≡ sub′
  oei-unique ozz ozz = refl
  oei-unique (oss sub) (oss sub′) = cong oss (oei-unique sub sub′)
  oei-unique (o′s sub) (o′s sub′) = cong o′s (oei-unique sub sub′)
