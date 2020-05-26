module Bin-predicates where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc; +-comm)

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
+-suc-suc m n rewrite +-suc (suc m) n | sym (+-assoc 1 m n) = refl

-- 変換の前後どちらでインクリメントしても結果は等しい
from∘inc≡suc∘from : ∀ (b : Bin) → from (inc b) ≡ suc (from b)
from∘inc≡suc∘from ⟨⟩ = refl
from∘inc≡suc∘from (b O) rewrite +-suc (from (b O)) zero | +-identityʳ (from (b O)) = refl
from∘inc≡suc∘from (b I) rewrite from∘inc≡suc∘from b | 2*n≡n+n (suc (from b)) | +-suc-suc (from b) (from b) | sym (2*n≡n+n (from b)) | +-comm 1 (2 * (from b)) = refl

data One : Bin → Set where
  ⟨⟩I : One (⟨⟩ I)
  _O : ∀ {b : Bin} → One b → One (b O)
  _I : ∀ {b : Bin} → One b → One (b I)

data Can : Bin → Set where
  ⟨⟩O : Can (⟨⟩ O)
  can : ∀ {b : Bin} → One b → Can b

-- Can b
-- ------------
-- Can (inc b)

inc-one : ∀ {b : Bin} → One b → One (inc b)
inc-one ⟨⟩I    = ⟨⟩I O
inc-one (ob O) = ob I
inc-one (ob I) = (inc-one ob) O

inc-can : ∀ {b : Bin} → Can b → Can (inc b)
inc-can ⟨⟩O          = can ⟨⟩I
inc-can (can ⟨⟩I)    = can (⟨⟩I O)
inc-can (can (ob O)) = can (ob I)
inc-can (can (ob I)) = can (inc-one (ob I))

-- ----------
-- Can (to n)

can-ℕ : ∀ (n : ℕ) → Can (to n)
can-ℕ zero    = ⟨⟩O
can-ℕ (suc n) = inc-can (can-ℕ n)

-- Can b
-- ---------------
-- to (from b) ≡ b

to∘from∘inc≡inc∘to∘from : ∀ (b : Bin) → to (from (inc b)) ≡ inc (to (from b))
to∘from∘inc≡inc∘to∘from ⟨⟩ =
  begin
    to (from (inc ⟨⟩))
  ≡⟨⟩
    to (from (⟨⟩ I))
  ≡⟨⟩
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ≡⟨⟩
    inc ⟨⟩
  ≡⟨⟩
    inc (to zero)
  ≡⟨⟩
    inc (to (from ⟨⟩))
  ∎
to∘from∘inc≡inc∘to∘from (b O) =
  begin
    to (from (inc (b O)))
  ≡⟨⟩
    to (from (b I))
  ≡⟨⟩
    to (2 * (from b) + 1)
  ≡⟨⟩
    to (2 * (from b) + (suc zero))
  ≡⟨ cong to (+-suc (2 * (from b)) zero) ⟩
    to (suc (2 * (from b) + zero))
  ≡⟨ cong (λ 2*fromb → to (suc 2*fromb)) (+-identityʳ (2 * (from b))) ⟩
    to (suc (2 * (from b)))
  ≡⟨⟩
    inc (to (2 * (from b)))
  ≡⟨⟩
    inc (to (from (b O)))
  ∎
to∘from∘inc≡inc∘to∘from (b I) =
  begin
    to (from (inc (b I)))
  ≡⟨⟩
    to (from ((inc b) O))
  ≡⟨⟩
    to (2 * (from (inc b)))
  ≡⟨ cong (λ suc∘fromb → to (2 * suc∘fromb)) (from∘inc≡suc∘from b) ⟩
    to (2 * (suc (from b)))
  ≡⟨ cong to (2*n≡n+n (suc (from b))) ⟩
    to ((suc (from b)) + (suc (from b)))
  ≡⟨ cong to (+-suc-suc (from b) (from b)) ⟩
    to (suc (suc ((from b) + (from b))))
  ≡⟨ cong (λ 2*fromb → to (suc (suc 2*fromb))) (sym (2*n≡n+n (from b))) ⟩
    to (suc (suc (2 * (from b))))
  ≡⟨ cong (λ 2*fromb+1 → to (suc 2*fromb+1)) (+-comm 1 (2 * (from b))) ⟩
    to (suc (2 * (from b) + 1))
  ≡⟨⟩
    to (suc (from (b I)))
  ≡⟨⟩
    inc (to (from (b I)))
  ∎

to∘from : ∀ {b : Bin} → Can b → to (from b) ≡ b
to∘from ⟨⟩O =
  begin
    to (from (⟨⟩ O))
  ≡⟨⟩
    to (2 * from ⟨⟩)
  ≡⟨⟩
    to (2 * zero)
  ≡⟨⟩
    to zero
  ≡⟨⟩
    ⟨⟩ O
  ∎
to∘from (can ⟨⟩I) =
  begin
    to (from (⟨⟩ I))
  ≡⟨⟩
    to (2 * from ⟨⟩ + 1)
  ≡⟨⟩
    to (2 * zero + 1)
  ≡⟨⟩
    to 1
  ≡⟨⟩
    ⟨⟩ I
  ∎
to∘from {b O} (can (ob O)) = {!!} -- TODO
to∘from {b I} (can (ob I)) =
  begin
    to (from (b I))
  ≡⟨⟩
    to (from (inc (b O)))
  ≡⟨ to∘from∘inc≡inc∘to∘from (b O) ⟩
    inc (to (from (b O)))
  ≡⟨ cong inc (to∘from (can (ob O))) ⟩
    inc (b O)
  ≡⟨⟩
    b I
  ∎
