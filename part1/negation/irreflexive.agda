module irreflexive where

open import Data.Nat using (ℕ; zero; suc)

open import Negation using (¬_)

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- n が非反射律 ∀ n ∈ ℕ, ¬(n < n) を満たすことの証明
<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n
