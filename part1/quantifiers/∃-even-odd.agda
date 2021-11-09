module ∃-even-odd where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-suc; +-comm)

open import Quantifiers using (Σ; ⟨_,_⟩; ∃; ∃-syntax; even; even-zero; even-suc; odd; odd-suc; ∃-even; ∃-odd)

-- 任意の自然数nについて、 m * 2 = n を満たす自然数mが存在するとき、nは偶数
∃-even′ : ∀ {n : ℕ} → ∃[ m ] (2 * m ≡ n) → even n

-- 任意の自然数nについて、 1 + m * 2 = n を満たす自然数mが存在するとき、nは奇数
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (1 + (2 * m) ≡ n) → odd n

postulate
  hoge : {m n : ℕ} → 2 * m + 1 ≡ m + 1 * suc m
  fuga : {m n : ℕ} → 2 * m ≡ m + 1 * suc m + 1

∃-even′ ⟨  zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩ = even-suc (∃-odd′ ⟨ m , {!!} ⟩)

-- ∃-odd′  ⟨  zero , refl ⟩ = odd-suc even-zero
-- ∃-odd′  ⟨ suc m , refl ⟩ = odd-suc (∃-even′ ⟨ m , fuga ⟩)
∃-odd′  ⟨     m , refl ⟩ = {!!}
