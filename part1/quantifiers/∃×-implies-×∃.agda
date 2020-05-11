module ∃×-implies-×∃ where

open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

-- 依存和型 (dependent sum type)
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- 存在量化子
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ (⟨ x , ⟨ bx , cx ⟩ ⟩) = ⟨ ⟨ x , bx ⟩ , ⟨ x , cx ⟩ ⟩

-- パターンマッチの左右で x の型が異なる
-- ×∃-implies-∃× : ∀ {A : Set} {B C : A → Set} →
--   (∃[ x ] B x) × (∃[ x ] C x) → ∃[ x ] (B x × C x)
-- ×∃-implies-∃× (⟨ ⟨ xˡ , bx ⟩ , ⟨ xʳ , cx ⟩ ⟩) = (⟨ xˡ , ⟨ bx , cx ⟩ ⟩)
