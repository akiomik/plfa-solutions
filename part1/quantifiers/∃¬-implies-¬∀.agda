open import Relation.Nullary using (¬_)

-- 依存和型 (dependent sum type)
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- 存在量化子 (existential quantifier)
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- 部分否定 ∃ x ¬ B(x) = ¬ ∀ x B(x) 
-- 「あるxについてはB(x)が成り立たない」とき、
-- 「すべてのxについてB(x)が成り立つ」というわけではない
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ x , ¬Bx ⟩ = λ{ xBx → ¬Bx (xBx x) }
