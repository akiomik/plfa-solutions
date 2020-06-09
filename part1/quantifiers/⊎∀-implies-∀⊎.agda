module ⊎∀-implies-∀⊎ where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set}
  → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
    -------------------------------------
  → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ hˡ) = inj₁ ∘ hˡ
⊎∀-implies-∀⊎ (inj₂ hʳ) = inj₂ ∘ hʳ

-- x と x₁ とで型が違う
-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
--    ∀ (x : A) → B x ⊎ C x → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- ∀⊎-implies-⊎∀ x (inj₁ bx) = inj₁ (λ x₁ → bx)
-- ∀⊎-implies-⊎∀ x (inj₂ cx) = inj₂ (λ x₁ → cx)
