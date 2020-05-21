module +-example where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Naturals using (suc; _+_)

+-example : 3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎
