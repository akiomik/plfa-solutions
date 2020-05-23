module *-comm where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)

open import Induction′ using (+-assoc; +-comm; +-suc)
open import +-swap using (+-swap)

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero zero = refl
*-comm zero (suc n) =
  begin
    zero * (suc n)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero + (zero * n)
  ≡⟨ *-comm zero n ⟩
    zero + (n * zero)
  ≡⟨⟩
    (suc n) * zero
  ∎
*-comm (suc m) zero =
  begin
    (suc m) * zero
  ≡⟨⟩
    zero + (m * zero)
  ≡⟨ *-comm m zero ⟩
    (zero * m)
  ≡⟨⟩
    zero
  ≡⟨⟩
    zero * (suc m)
  ∎
*-comm (suc m) (suc n) =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-comm m (suc n)) ⟩
    (suc n) + ((suc n) * m)
  ≡⟨⟩
    (suc n) + (m + (n * m))
  ≡⟨ +-swap (suc n) m (n * m) ⟩
    m + ((suc n) + (n * m))
  ≡⟨ sym (+-assoc m (suc n) (n * m)) ⟩
    (m + (suc n)) + (n * m)
  ≡⟨ cong (_+ (n * m)) (+-suc m n) ⟩
    suc (m + n) + (n * m)
  ≡⟨ cong suc (+-assoc m n (n * m)) ⟩
    (suc m) + (n + (n * m))
  ≡⟨ cong (λ m*n → (suc m) + (n + m*n)) (*-comm n m) ⟩
    (suc m) + (n + (m * n))
  ≡⟨⟩
    (suc m) + ((suc m) * n)
  ≡⟨ cong ((suc m) +_) (*-comm ((suc m)) n) ⟩
    (suc m) + (n * (suc m))
  ≡⟨⟩
    (suc n) * (suc m)
  ∎
