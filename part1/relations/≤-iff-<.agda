module ≤-iff-< where

open import Data.Nat using (ℕ; zero; suc)

open import Relations using (_≤_; z≤n; s≤s; _<_; z<s; s<s)

-- m + 1 ≤ n ならば m < n になることの証明
≤-iff-< : ∀ (m n : ℕ)
  → suc m ≤ n
    ---------
  → m < n
≤-iff-< zero    n       (s≤s _)   = z<s
≤-iff-< (suc m) (suc n) (s≤s m≤n) = s<s (≤-iff-< m n m≤n)

-- m + 1 ≤ n ならば m < n になることの証明 (implicit版)
≤-iff-<′ : ∀ {m n : ℕ}
  → suc m ≤ n
    ---------
  → m < n
≤-iff-<′ (s≤s z≤n)       = z<s
≤-iff-<′ (s≤s (s≤s m≤n)) = s<s (≤-iff-<′ (s≤s m≤n))
