module ⊎-weak-× where

open import Connectives using (_⊎_; inj₁; inj₂; _×_; ⟨_,_⟩)

-- 弱い分配法則
-- fromが提供できないため同型や埋め込みにならない
⊎-weak-× : ∀ {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ a , c ⟩ = inj₁ a
⊎-weak-× ⟨ inj₂ b , c ⟩ = inj₂ ⟨ b , c ⟩
