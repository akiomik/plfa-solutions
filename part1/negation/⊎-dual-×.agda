module ⊎-dual-× where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)

open import Negation using (_≃_; extensionality; ¬_)

-- 選言削除 (proof by cases)
-- case-⊎ : ∀ {A B C : Set}
--   → (A → C)
--   → (B → C)
--   → A ⊎ B
--     -----
--   → C
-- case-⊎ f g (inj₁ x) = f x
-- case-⊎ f g (inj₂ y) = g y

-- 関数 h を使った選言削除と、h の適用とが等しいことの証明
uniq-⊎ : ∀ {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

-- 射 f : X → Y
⊎-dual-×-to : ∀ {A B : Set} → ¬ (A ⊎ B) → (¬ A) × (¬ B)
⊎-dual-×-to ¬a⊎b = (λ a → ¬a⊎b (inj₁ a)) , (λ b → ¬a⊎b (inj₂ b))

-- 射 g : Y → X
-- NOTE: そのままだと途中でパターンマッチを含むλが出てきて式変形できなくなるので、
--       case-⊎ としてパターンマッチを型にするのがポイント
⊎-dual-×-from : ∀ {A B : Set} → (¬ A) × (¬ B) → ¬ (A ⊎ B)
⊎-dual-×-from (¬a , ¬b) = case-⊎ ¬a ¬b

-- 左逆射 g ∘ f = id_X を持つことの証明
⊎-dual-×-from∘to : ∀ {A B : Set} → (¬a⊎b : ¬ (A ⊎ B)) →
  (⊎-dual-×-from ∘ ⊎-dual-×-to) ¬a⊎b ≡ ¬a⊎b
⊎-dual-×-from∘to ¬a⊎b = (extensionality ∘ uniq-⊎) ¬a⊎b

-- 右逆射 f ∘ g = id_Y を持つことの証明
⊎-dual-×-to∘from : ∀ {A B : Set} → (¬a×¬b : (¬ A) × (¬ B)) →
  (⊎-dual-×-to ∘ ⊎-dual-×-from) ¬a×¬b ≡ ¬a×¬b
⊎-dual-×-to∘from ¬a×¬b = refl

-- ド・モルガンの双対性の証明
⊎-dual-× : ∀ {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = ⊎-dual-×-to
    ; from = ⊎-dual-×-from
    ; from∘to = ⊎-dual-×-from∘to
    ; to∘from = ⊎-dual-×-to∘from
    }
