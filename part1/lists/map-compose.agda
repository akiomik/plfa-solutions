module map-compose where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Function using (_∘_)

postulate
  -- 外延性の公理
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- リスト
infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

-- map
map : ∀ {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

-- 外延性の公理を用いた証明のための補助定理
lemma : ∀ {A B C : Set} → (f : A → B) → (g : B → C) → (x : List A)
  → map (g ∘ f) x ≡ (map g ∘ map f) x
lemma f g []       = refl
lemma f g (x ∷ xs) =
  begin
    map (g ∘ f) (x ∷ xs)
  ≡⟨⟩
    (g ∘ f) x ∷ map (g ∘ f) xs
  ≡⟨ cong ((g ∘ f) x ∷_) (lemma f g xs) ⟩
    (g ∘ f) x ∷ (map g ∘ map f) xs
  ≡⟨⟩
    (map g ∘ map f) (x ∷ xs)
  ∎

-- mapの分配法則の証明
map-compose : ∀ {A B C : Set} → (f : A → B) → (g : B → C)
  → map (g ∘ f) ≡ map g ∘ map f
map-compose f g = extensionality (lemma f g)
