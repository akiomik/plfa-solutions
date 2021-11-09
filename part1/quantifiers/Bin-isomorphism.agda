module Bin-isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc; +-comm)

open import Quantifiers using (_≃_; ⟨_,_⟩; ∃-syntax)

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

-- from (to n) ≡ n
from∘to : ∀ (n : ℕ) → from (to n) ≡ n
from∘to zero = refl
from∘to (suc n) rewrite from∘inc≡suc∘from (to n) = cong suc (from∘to n)

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
to∘from∘inc≡inc∘to∘from ⟨⟩                                                                                                                                                                                                        = refl
to∘from∘inc≡inc∘to∘from (b O) rewrite +-suc (2 * (from b)) zero | +-identityʳ (2 * (from b))                                                                                                                                      = refl
to∘from∘inc≡inc∘to∘from (b I) rewrite from∘inc≡suc∘from b | cong to (2*n≡n+n (suc (from b))) | cong to (+-suc-suc (from b) (from b)) | sym (2*n≡n+n (from b)) | cong (λ 2*fromb+1 → to (suc 2*fromb+1)) (+-comm 1 (2 * (from b))) = refl

hoge : ∀ {b : Bin}→ ℕ ≃ ∃[ b ](Can b)
hoge =
  record
    { to      = λ n → ⟨ to n , can-ℕ n ⟩
    ; from    = λ{ (⟨ b , Canb ⟩) → from b }
    ; from∘to = {!!}
    ; to∘from = {!!}
    }
