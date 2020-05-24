module <-trans-revisited where

open import Data.Nat using (ℕ; suc)

open import Relations using (_≤_; z≤n; s≤s; ≤-trans; _<_; z<s; s<s)
open import ≤-iff-< using (≤-iff-<′)

<-iff-≤ : ∀ {m n : ℕ}
  → m < n
    ---------
  → suc m ≤ n
<-iff-≤ z<s       = s≤s z≤n
<-iff-≤ (s<s m<n) = s≤s (<-iff-≤ m<n)

-- <-trans の別証明 (≤-trans版)
<-trans-revisited : ∀ {m n p : ℕ}
  → m < n
  → n < p
    -----
  → m < p
<-trans-revisited z<s       (s<s n<p) = ≤-iff-<′ (≤-trans (<-iff-≤ z<s) (<-iff-≤ (s<s n<p)))
<-trans-revisited (s<s m<n) (s<s n<p) = ≤-iff-<′ (≤-trans (s≤s (<-iff-≤ (lemma m<n))) (<-iff-≤ (s<s n<p)))
  where
    lemma : ∀ {m n : ℕ}
      → m < n
        ---------
      → m < suc n
    lemma z<s       = z<s
    lemma (s<s m<n) = s<s (lemma m<n)
