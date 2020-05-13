module sum-downFrom where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (*-suc; *-identityʳ; *-distribʳ-+; *-distribˡ-∸; +-∸-assoc; +-∸-comm; m+n∸n≡m; m≤m+n; m≤m*n)

open import lists using (List; []; _∷_; [_,_,_]; sum)

-- (n - 1), ⋯ , 0 を返す
downFrom : ℕ → List ℕ
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

n≤n*n : ∀ (n : ℕ) → n ≤ n * n
n≤n*n zero    = z≤n
n≤n*n (suc n) = m≤m*n (suc n) (s≤s z≤n)

-- (n - 1) + ⋯ + 0 と n * (n ∸ 1) / 2 が等しいことの証明
sum-downFrom : ∀ (n : ℕ) → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero =
  begin
    sum (downFrom zero) * 2
  ≡⟨⟩
    sum [] * 2
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * (zero ∸ 1)
  ∎
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    sum (n ∷ downFrom n) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩ -- * 2 の分配
    (n * 2) + (sum (downFrom n)) * 2
  ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩ -- 帰納法
    (n * 2) + (n * (n ∸ 1))
  ≡⟨ cong (n * 2 +_) (*-distribˡ-∸ n n 1) ⟩ -- n * の分配
    (n * 2) + (n * n ∸ n * 1)
  ≡⟨ cong (λ n*1 → n * 2 + (n * n ∸ n*1)) (*-identityʳ n) ⟩ -- * 1 の除去
    (n * 2) + (n * n ∸ n)
  ≡⟨ sym (+-∸-assoc (n * 2) (n≤n*n n)) ⟩ -- 結合法則
    (n * 2) + n * n ∸ n
  ≡⟨ cong (λ n*2 → n*2 + n * n ∸ n) (*-suc n 1) ⟩ -- 積の展開
    (n + n * 1) + n * n ∸ n
  ≡⟨ cong (λ n*1 → n + n*1 + n * n ∸ n) (*-identityʳ n) ⟩ -- * 1 の除去
    (n + n) + n * n ∸ n
  ≡⟨ +-∸-comm (n * n) (m≤m+n n n) ⟩ -- 交換法則
    (n + n) ∸ n + n * n
  ≡⟨ cong (_+ n * n) (m+n∸n≡m n n) ⟩ -- n ∸ n の除去
    n + n * n
  ≡⟨⟩
    -- = n * (suc n)
    -- = (suc n) * n
    (suc n) * ((suc n) ∸ 1)
  ∎
