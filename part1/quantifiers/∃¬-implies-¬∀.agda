module ∃¬-implies-¬∀ where

open import Relation.Nullary using (¬_)

open import Quantifiers using (⟨_,_⟩; ∃-syntax)

-- 部分否定 ∃ x ¬ B(x) = ¬ ∀ x B(x) 
-- 「あるxについてはB(x)が成り立たない」とき、
-- 「すべてのxについてB(x)が成り立つ」というわけではない
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ xBx → ¬Bx (xBx x)
