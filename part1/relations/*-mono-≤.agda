module *-mono-≤ where

open import Data.Nat using (ℕ; zero; suc; _*_)
open import Data.Nat.Properties using (*-comm)

open import Relations using (_≤_; z≤n; ≤-trans; +-mono-≤)

-- ((suc n) * p) ≤ ((suc n) * q) は (p + n * p) ≤ (q + n * q) であることから
-- p ≤ q と (n * p) ≤ (n * q) が成り立てば +-mono-≤ により証明できる
*-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    -------------
  → n * p ≤ n * q
*-monoʳ-≤ zero    p q z≤z = z≤n
*-monoʳ-≤ (suc n) p q p≤q = +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    -------------
  → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    -------------
  → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)
