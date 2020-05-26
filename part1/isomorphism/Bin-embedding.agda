module Bin-embedding where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-comm; +-assoc)

open import Isomorphism using (_≲_)

-- 2進数の表現
data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

-- 2進数のインクリメント
inc : Bin → Bin
inc ⟨⟩    = ⟨⟩ I
inc (b O) = b I
inc (b I) = inc b O

-- 自然数から2進数への変換
to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

-- 2進数から自然数への変換
from : Bin → ℕ
from ⟨⟩    = zero
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

2*n≡n+n : ∀ (n : ℕ) → 2 * n ≡ n + n
2*n≡n+n n rewrite +-identityʳ n = refl

+-suc-suc : ∀ (m n : ℕ) → (suc m) + (suc n) ≡ suc (suc (m + n))
+-suc-suc m n rewrite +-suc (suc m) n | +-assoc 1 m n = refl

from∘inc≡suc∘from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from∘inc≡suc∘from ⟨⟩ = refl
from∘inc≡suc∘from (b O) rewrite +-suc (from (b O)) zero = cong suc (+-identityʳ (from (b O)))
from∘inc≡suc∘from (b I) rewrite from∘inc≡suc∘from b | 2*n≡n+n (suc (from b)) | +-suc-suc (from b) (from b) | sym (2*n≡n+n (from b)) | +-comm 1 (2 * (from b)) = refl

from∘to : ∀ (n : ℕ) → from (to n) ≡ n
from∘to zero = refl
from∘to (suc n) rewrite from∘inc≡suc∘from (to n) = cong suc (from∘to n)

Bin-embedding : ℕ ≲ Bin
Bin-embedding =
  record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    }
