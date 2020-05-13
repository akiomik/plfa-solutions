module sum-downFrom where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; s≤s; z≤n; _<_)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ; *-distribʳ-+; *-distribˡ-+; +-∸-assoc; m+n∸m≡n; m+[n∸m]≡n; m+n∸n≡m; +-∸-comm; *-distribˡ-∸; *-distribʳ-∸; *-suc; +-comm; m≤m+n; m≤m*n)

open import lists using (List; []; _∷_; [_]; [_,_,_]; sum; foldr)

downFrom : ℕ → List ℕ
downFrom zero    = []
downFrom (suc n) = n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

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
sum-downFrom (suc zero) =
  begin
    sum (downFrom (suc zero)) * 2
  ≡⟨⟩
    sum (zero ∷ downFrom zero) * 2
  ≡⟨⟩
    (zero + sum (downFrom zero)) * 2
  ≡⟨⟩
    (zero + sum []) * 2
  ≡⟨⟩
    (zero + zero) * 2
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * (zero ∸ 1)
  ∎
sum-downFrom (suc (suc n)) =
  begin
    sum (downFrom (suc (suc n))) * 2
  ≡⟨⟩
    sum ((suc n) ∷ downFrom (suc n)) * 2
  ≡⟨⟩
    ((suc n) + sum (downFrom (suc n))) * 2
  ≡⟨ *-distribʳ-+ 2 (suc n) (sum (downFrom (suc n))) ⟩ -- * 2 の分配
    ((suc n) * 2) + ((sum (downFrom (suc n))) * 2)
  ≡⟨ cong ((suc n) * 2 +_) (sum-downFrom (suc n)) ⟩ -- 帰納法
    ((suc n) * 2) + ((suc n) * ((suc n) ∸ 1))
  ≡⟨ cong (_+ ((suc n) * ((suc n) ∸ 1))) (*-suc (suc n) 1) ⟩ -- (suc n) * 2 = (suc n) + (suc n) * 1
    (suc n) + (suc n) * 1 + ((suc n) * ((suc n) ∸ 1))
  ≡⟨ cong (λ n*1 → (suc n) + n*1 + ((suc n) * ((suc n) ∸ 1))) (*-identityʳ (suc n)) ⟩ -- * 1 の除去
    (suc n) + (suc n) + ((suc n) * ((suc n) ∸ 1))
  ≡⟨ cong ((suc n) + (suc n) +_) (*-distribˡ-∸ (suc n) (suc n) 1) ⟩ -- (suc n) * の分配
    (suc n) + (suc n) + ((suc n) * (suc n) ∸ (suc n) * 1)
  ≡⟨ cong (λ n*1 → (suc n) + (suc n) + ((suc n) * (suc n) ∸ n*1)) (*-identityʳ (suc n)) ⟩ -- * 1 の除去
    (suc n) + (suc n) + (((suc n) * (suc n)) ∸ (suc n))
  ≡⟨ +-assoc (suc n) (suc n) ((suc n) * (suc n) ∸ (suc n)) ⟩ -- 結合法則
    (suc n) + ((suc n) + (((suc n) * (suc n)) ∸ (suc n)))
  ≡⟨ cong ((suc n) +_) (m+[n∸m]≡n (m≤m*n (suc n) (s≤s z≤n))) ⟩ -- (suc n) ∸ (suc n) の除去 (n ≥ 1のとき)
    (suc n) + (suc n) * (suc n)
  ≡⟨⟩
    -- (suc n) + (suc n) * (suc n)
    -- (suc n) * (suc (suc n))
    -- (suc (suc n)) * (suc n)
    -- (suc (suc n)) + (suc (suc n)) * (suc n) ∸ (suc (suc n))
    -- (suc (suc n)) * (suc (suc n)) ∸ (suc (suc n))
    (suc (suc n)) * ((suc (suc n)) ∸ 1)
  ∎
