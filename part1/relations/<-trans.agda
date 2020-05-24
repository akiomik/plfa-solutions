module <-trans where

open import Data.Nat using (ℕ)

open import Relations using (_<_; z<s; s<s)

<-trans : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans z<s     (s<s _) = z<s
<-trans (s<s a) (s<s b) = s<s (<-trans a b)
