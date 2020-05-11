module ∃-distrib-⊎ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import plfa.part1.Isomorphism using (_≃_; extensionality)

-- 同型 (isomorphism)
infix 0 _≃_
record _≃_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A
    from∘to : ∀ (x : A) → from (to x) ≡ x
    to∘from : ∀ (y : B) → to (from y) ≡ y
open _≃_

-- 依存和型 (dependent sum type)
data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

-- 存在量化子 (existential quantifier)
∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B
 
-- 存在量化子の分配性の証明
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
    { to      = λ{ (⟨ x , (inj₁ b) ⟩) → inj₁ ⟨ x , b ⟩
                 ; (⟨ x , (inj₂ c) ⟩) → inj₂ ⟨ x , c ⟩ }
    ; from    = λ{ (inj₁ ⟨ x , b ⟩) → ⟨ x , (inj₁ b) ⟩
                 ; (inj₂ ⟨ x , c ⟩) → ⟨ x , (inj₂ c) ⟩ }
    ; from∘to = λ{ (⟨ x , (inj₁ b) ⟩) → refl
                 ; (⟨ x , (inj₂ c) ⟩) → refl }
    ; to∘from = λ{ (inj₁ ⟨ x , b ⟩) → refl
                 ; (inj₂ ⟨ x , c ⟩) → refl }
    }
