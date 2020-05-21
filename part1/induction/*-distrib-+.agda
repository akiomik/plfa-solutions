module *-distrib-+ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Induction′ using (+-assoc; +-comm; +-suc)

-- 積が和に対して分配的であることの証明
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p =
  begin
    (zero + n) * p
  ≡⟨⟩
    n * p
  ≡⟨⟩
    zero * p + n * p
  ∎
*-distrib-+ (suc m) n p =
  begin
    ((suc m) + n) * p
  ≡⟨ cong (_* p) (+-comm (suc m) n) ⟩
    (n + (suc m)) * p
  ≡⟨ cong (_* p) (+-suc n m) ⟩
    (suc (n + m)) * p
  ≡⟨⟩
    p + ((n + m) * p)
  ≡⟨ cong (p +_) (*-distrib-+ n m p) ⟩
    p + (n * p + m * p)
  ≡⟨ cong (p +_) (+-comm (n * p) (m * p)) ⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    (p + (m * p)) + n * p
  ≡⟨⟩
    (suc m) * p + n * p
  ∎
