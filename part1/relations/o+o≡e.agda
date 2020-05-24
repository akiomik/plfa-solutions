module o+o≡e where

open import Data.Nat using (ℕ; _+_)

open import Relations using (even; odd; zero; suc)

-- 奇数+奇数は偶数
o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
    -----
  → even (m + n)
o+o≡e (suc zero)     on = suc on
o+o≡e (suc (suc em)) on = suc (suc (o+o≡e em on))
