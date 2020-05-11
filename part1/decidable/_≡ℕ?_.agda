module _≡ℕ?_ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import decidable using (Dec; yes; no)

-- 0と等しい1以上の自然数は存在しない
¬z≡n : ∀ {n : ℕ} → ¬ (zero ≡ suc n)
¬z≡n ()
¬m≡z : ∀ {m : ℕ} → ¬ (suc m ≡ zero)
¬m≡z ()

-- m = n が成り立てば (m + 1) = (n + 1) も成り立つ
s≡s : ∀ {m n : ℕ} → m ≡ n → suc m ≡ suc n
s≡s refl = refl

-- m = n が成り立たなければ (m + 1) = (n + 1) も成り立たない
¬s≡s : ∀ {m n : ℕ} → ¬ (m ≡ n) → ¬ (suc m ≡ suc n)
¬s≡s ¬m≡n refl = ¬m≡n refl

-- decidableを使った、2つの自然数が等しいかどうか判定する関数
_≡ℕ?_ : ∀ (m n : ℕ) → Dec (m ≡ n)
zero  ≡ℕ? zero               = yes refl
zero  ≡ℕ? suc n              = no ¬z≡n
suc m ≡ℕ? zero               = no ¬m≡z
suc m ≡ℕ? suc n with m ≡ℕ? n
...                | yes m≡n = yes (s≡s m≡n)
...                | no ¬m≡n = no (¬s≡s ¬m≡n)
