# thinning
A collection of things I know about thinnings.
The original concept and most of the lemmas are gleaned from Conor McBride's impromptu talks.
A thinning is an order-preserving embedding of one list into another.
Equivalently, `m ≤ n` (the thinnings from `m` to `n`) are the monotone injections from `Fin m` to `Fin n`.
These are coded up as the following inductive data type.

```agda
data _≤_ : (m n : ℕ) → Set where
  oz :                    zero ≤ zero   -- end
  os : ∀ {m n} → m ≤ n → suc m ≤ suc n  -- keep
  o′ : ∀ {m n} → m ≤ n →     m ≤ suc n  -- drop
```

Ignoring the indices, this makes thinnings a list of bits (`os` vs `o′`), terminated by `oz`.
Those bits say whether to keep (`os`) or drop (`o′`) the head of the source list when producing the list embedded into it.
`n` tracks the length of the source list, and `m` tracks the number of keep instructions, i.e, the length of the target list.

`m ≤ n` has `n` choose `m` inhabitants when `m` is less than or equal to `n`, and 0 inhabitants otherwise.
In particular, `1 ≤ n` has `n` inhabitants, and can be used in place of `Fin n`.
If de Bruijn indices in a scope of size `m` are represented as inhabitants of `1 ≤ m`, then these can be turned into indices in a scope of size `n` by composition of thinnings `1 ≤ m` and `m ≤ n`.

## Dependencies &c

* I depend on [agda-stdlib](https://github.com/agda/agda-stdlib) for some simple things about natural numbers and equality.
* I depend on [egads](https://github.com/laMudri/egads) (my nascent library for category theory) only in files named `Category.agda`, so if you can't be bothered setting that up, just remove it from the `.agda-lib` file and don't try checking those files.
* I use exotic Unicode characters just to mess with Conor.
  More seriously, I'm less confident in my ASCII art abilities, and like to use standard names for things (particularly well established set theory things) wherever possible.
