module Bin-laws where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; sym; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Induction′ using (+-suc; +-identityʳ; +-comm; +-assoc)

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
2*n≡n+n n =
  begin
    2 * n
  ≡⟨⟩
    n + (1 * n)
  ≡⟨⟩
    n + (n + (0 * n))
  ≡⟨⟩
    n + (n + 0)
  ≡⟨ cong (n +_) (+-identityʳ n) ⟩
    n + n
  ∎

+-suc-suc : ∀ (m n : ℕ) → (suc m) + (suc n) ≡ suc (suc (m + n))
+-suc-suc m n =
  begin
    (suc m) + (suc n)
  ≡⟨ +-suc (suc m) n ⟩
    suc ((suc m) + n)
  ≡⟨ cong suc (sym (+-assoc 1 m n)) ⟩
    suc (suc (m + n))
  ∎

-- 変換の前後どちらでインクリメントしても結果は等しい
from∘inc≡suc∘from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from∘inc≡suc∘from ⟨⟩ =
  begin
    from (inc ⟨⟩)
  ≡⟨⟩
    from (⟨⟩ I)
  ≡⟨⟩
    suc zero
  ≡⟨⟩
    suc (from ⟨⟩)
  ∎
from∘inc≡suc∘from (b O) =
  begin
    from (inc (b O))
  ≡⟨⟩
    from (b I)
  ≡⟨⟩
    2 * (from b) + 1
  ≡⟨⟩
    from (b O) + 1
  ≡⟨ +-suc (from (b O)) zero ⟩
    suc (from (b O) + zero)
  ≡⟨ cong suc (+-identityʳ (from (b O))) ⟩
    suc (from (b O))
  ∎
from∘inc≡suc∘from (b I) =
  begin
    from (inc (b I))
  ≡⟨⟩
    from ((inc b) O)
  ≡⟨⟩
    2 * (from (inc b))
  ≡⟨ cong (2 *_) (from∘inc≡suc∘from b) ⟩
    2 * (suc (from b))
  ≡⟨ 2*n≡n+n (suc (from b)) ⟩
    (suc (from b)) + (suc (from b))
  ≡⟨ +-suc-suc (from b) (from b) ⟩
    suc (suc ((from b) + (from b)))
  ≡⟨ cong (λ 2*fromb → suc (suc 2*fromb)) (sym (2*n≡n+n (from b))) ⟩
    suc (suc (2 * (from b)))
  ≡⟨ cong suc (+-comm 1 (2 * (from b))) ⟩
    suc (2 * (from b) + 1)
  ≡⟨⟩
    suc (from (b I))
  ∎

-- to∘from : ∀ (b : Bin) → to (from b) ≡ b
-- to∘from ⟨⟩ = {!!} -- (to zero) が (⟨⟩ O) にエンコードされるため成り立たない
-- to∘from (b O) = {!!}
-- to∘from (b I) = {!!}

from∘to : ∀ (n : ℕ) → from (to n) ≡ n
from∘to zero =
  begin
    from (to zero)
  ≡⟨⟩
    from (⟨⟩ O)
  ≡⟨⟩
    2 * (from ⟨⟩)
  ≡⟨⟩
    2 * zero
  ≡⟨⟩
    zero
  ∎
from∘to (suc n) =
  begin
    from (to (suc n))
  ≡⟨⟩
    from (inc (to n))
  ≡⟨ from∘inc≡suc∘from (to n) ⟩
    suc (from (to n))
  ≡⟨ cong suc (from∘to n) ⟩
    suc n
  ∎
