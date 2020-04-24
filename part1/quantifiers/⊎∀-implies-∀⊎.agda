module ⊎∀-implies-∀⊎ where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x) → ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ hˡ) = inj₁ ∘ hˡ
⊎∀-implies-∀⊎ (inj₂ hʳ) = inj₂ ∘ hʳ

-- パターンマッチがうまくいかない
-- ∀⊎-implies-⊎∀ : ∀ {A : Set} {B C : A → Set} →
--    ∀ (x : A) → B x ⊎ C x → (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)
-- ∀⊎-implies-⊎∀ (λ x → inj₁ hˡ) = inj₁ ∘ hˡ
-- ∀⊎-implies-⊎∀ (λ x → inj₂ hʳ) = inj₂ ∘ hʳ
