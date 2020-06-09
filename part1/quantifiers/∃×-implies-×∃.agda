module ∃×-implies-×∃ where

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import Quantifiers using (⟨_,_⟩; ∃-syntax)

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set}
  → ∃[ x ] (B x × C x)
    ---------------------------
  → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ (⟨ x , ⟨ bx , cx ⟩ ⟩) = ⟨ ⟨ x , bx ⟩ , ⟨ x , cx ⟩ ⟩

-- パターンマッチの左右で x の型が異なる
-- ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
--   (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
-- ×∃-implies-∃× (⟨ ⟨ xˡ , bx ⟩ , ⟨ xʳ , cx ⟩ ⟩) = (⟨ xˡ , ⟨ bx , cx ⟩ ⟩)
