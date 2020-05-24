module trichotomy where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)

open import Relations using (_<_; z<s; s<s)

-- 三分法
data Trichotomy (m n : ℕ) : Set where
  m<n : m < n → Trichotomy m n
  m≡n : m ≡ n → Trichotomy m n
  n<m : n < m → Trichotomy m n

trichotomy : ∀ (m n : ℕ) → Trichotomy m n
trichotomy zero    zero                        = m≡n refl
trichotomy (suc m) zero                        = n<m z<s
trichotomy zero    (suc n)                     = m<n z<s
trichotomy (suc m) (suc n) with trichotomy m n
...                           | m<n m′<n′      = m<n (s<s m′<n′)
...                           | m≡n refl       = m≡n refl
...                           | n<m n′<m′      = n<m (s<s n′<m′)
