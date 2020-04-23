module stable where

open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x = λ{¬x → ¬x x}

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

¬-stable : ∀ {A : Set} → Stable (¬ A)
¬-stable = λ{ ¬¬¬a → λ{ a → ¬¬¬a (λ ¬a → ¬a a) }}
-- ¬-stable = ¬¬¬-elim

×-stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×-stable sa sb = λ ¬¬a×b →
    (sa λ{ ¬a → ¬¬a×b λ{ a×b → ¬a (proj₁ a×b) }})
  , (sb λ{ ¬b → ¬¬a×b λ{ a×b → ¬b (proj₂ a×b) }})
