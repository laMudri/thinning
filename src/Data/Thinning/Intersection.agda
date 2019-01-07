module Data.Thinning.Intersection where

  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Product hiding (<_,_>)

  open import Data.Thinning
  open import Data.Thinning.Sub
  open import Data.Thinning.Unsized

  infixr 6 _∩_

  -- Intersection of sets
  -- Elements are kept iff they are kept by both of the two thinnings.
  _∩_ : ∀ {n} (X Y : ThSet n) → ThSet n
  (.zero ,   oz) ∩        Y       = Y
  (    l , o′ θ) ∩ (    m , o′ φ) = u′ ((l , θ) ∩ (m , φ))
  (    l , o′ θ) ∩ (suc m , os φ) = u′ ((l , θ) ∩ (m , φ))
  (suc l , os θ) ∩ (    m , o′ φ) = u′ ((l , θ) ∩ (m , φ))
  (suc l , os θ) ∩ (suc m , os φ) = us ((l , θ) ∩ (m , φ))

  fst : ∀ {n} {X Y : ThSet n} → X ∩ Y ⊆u X
  fst {X = _ ,   oz} {_ ,   oz} = ozz
  fst {X = _ , os θ} {_ , os φ} = oss fst
  fst {X = _ , os θ} {_ , o′ φ} = o′s fst
  fst {X = _ , o′ θ} {_ , os φ} = o′′ fst
  fst {X = _ , o′ θ} {_ , o′ φ} = o′′ fst

  snd : ∀ {n} {X Y : ThSet n} → X ∩ Y ⊆u Y
  snd {X = _ ,   oz} {_ ,   oz} = ozz
  snd {X = _ , os θ} {_ , os φ} = oss (snd {X = _ , θ})
  snd {X = _ , os θ} {_ , o′ φ} = o′′ (snd {X = _ , θ})
  snd {X = _ , o′ θ} {_ , os φ} = o′s (snd {X = _ , θ})
  snd {X = _ , o′ θ} {_ , o′ φ} = o′′ (snd {X = _ , θ})

  <_,_> : ∀ {n} {X Y A : ThSet n} → A ⊆u X → A ⊆u Y → A ⊆u X ∩ Y
  < ozz , AY > = AY
  < oss AX , oss AY > = oss < AX , AY >
  < o′s AX , o′s AY > = o′s < AX , AY >
  < o′s AX , o′′ AY > = o′′ < AX , AY >
  < o′′ AX , o′s AY > = o′′ < AX , AY >
  < o′′ AX , o′′ AY > = o′′ < AX , AY >
