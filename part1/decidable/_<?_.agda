module _<?_ where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import decidable using (Dec; yes; no)

-- 厳密な不等式 (strict inequality)
infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

-- 0未満の自然数は存在しない
¬m<z : ∀ {m : ℕ} → ¬ (m < zero)
¬m<z ()

-- m < n が成り立たなければ (m + 1) < (n + 1) も成り立たない
¬s<s : ∀ {m n : ℕ} → ¬ (m < n) → ¬ (suc m < suc n)
¬s<s ¬m<n (s<s m<n) = ¬m<n m<n

-- decidableを使った厳密な不等式
_<?_ : ∀ (m n : ℕ) → Dec (m < n)
m     <? zero                = no ¬m<z
zero  <? suc n               = yes z<s
suc m <? suc n with m <? n
...               | yes m<n  = yes (s<s m<n)
...               | no  ¬m<n = no (¬s<s ¬m<n)
