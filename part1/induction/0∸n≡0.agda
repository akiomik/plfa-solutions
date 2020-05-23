module 0∸n≡0 where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _∸_)

0∸n≡0 : ∀ (n : ℕ) → zero ∸ n ≡ zero
0∸n≡0 zero =
  begin
    zero ∸ zero
  ≡⟨⟩
    zero
  ∎
0∸n≡0 (suc n) =
  begin
    zero ∸ (suc n)
  ≡⟨⟩
    zero
  ∎
