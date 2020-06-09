module Stable where

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import Negation using (¬_; ¬¬¬-elim)

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = λ ¬¬¬a → (λ a → ¬¬¬a (λ ¬a → ¬a a))
-- ¬-stable = ¬¬¬-elim

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable sa sb = λ ¬¬a×b →
  ⟨ (sa λ{ ¬a → ¬¬a×b λ{ a×b → ¬a (proj₁ a×b) }})
  , (sb λ{ ¬b → ¬¬a×b λ{ a×b → ¬b (proj₂ a×b) }})
  ⟩
