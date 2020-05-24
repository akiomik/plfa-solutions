module Bin where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Naturals using (ℕ; zero; suc; _+_; _*_)

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

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

_ : inc (⟨⟩ O O O O) ≡ ⟨⟩ O O O I
_ = refl

_ : inc (⟨⟩ O O O I) ≡ ⟨⟩ O O I O
_ = refl

_ : inc (⟨⟩ O O I O) ≡ ⟨⟩ O O I I
_ = refl

_ : inc (⟨⟩ O O I I) ≡ ⟨⟩ O I O O
_ = refl

_ : inc (⟨⟩ O I O O) ≡ ⟨⟩ O I O I
_ = refl

-- 自然数から2進数への変換
to : ℕ → Bin
to zero    = ⟨⟩ O
to (suc n) = inc (to n)

_ : to 0 ≡ ⟨⟩ O
_ = refl

_ : to 1 ≡ ⟨⟩ I
_ = refl

_ : to 2 ≡ ⟨⟩ I O
_ = refl

_ : to 3 ≡ ⟨⟩ I I
_ = refl

_ : to 4 ≡ ⟨⟩ I O O
_ = refl

-- 2進数から自然数への変換
from : Bin → ℕ
from ⟨⟩    = zero
from (b O) = 2 * (from b)
from (b I) = 2 * (from b) + 1

_ : from (⟨⟩ O) ≡ 0
_ = refl

_ : from (⟨⟩ I) ≡ 1
_ = refl

_ : from (⟨⟩ I O) ≡ 2
_ = refl

_ : from (⟨⟩ I I) ≡ 3
_ = refl

_ : from (⟨⟩ I O O) ≡ 4
_ = refl
