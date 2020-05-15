module foldr-monoid-foldl where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; foldr; IsMonoid)
open IsMonoid
open import foldl using (foldl)

postulate
  -- 外延性の公理
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- foldr-monoidのfoldl版
-- _⊗_ と e がモノイドをなすとき、任意の値でfoldを再表現できる
foldl-monoid : ∀ {A : Set} → (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ (foldl _⊗_ e xs)
foldl-monoid _⊗_ e ⊗-monoid [] y =
  begin
    foldl _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityʳ ⊗-monoid y) ⟩
    y ⊗ e
  ≡⟨⟩
    y ⊗ (foldl _⊗_ e [])
  ∎
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ (foldl _⊗_ e xs)
  ≡⟨ assoc ⊗-monoid y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ (foldl _⊗_ e xs))
  ≡⟨ cong (y ⊗_) (sym (foldl-monoid _⊗_ e ⊗-monoid xs x)) ⟩
    y ⊗ (foldl _⊗_ x xs)
  ≡⟨ cong (λ e⊗x → y ⊗ (foldl _⊗_ e⊗x xs)) (sym (identityˡ ⊗-monoid x)) ⟩
    y ⊗ (foldl _⊗_ (e ⊗ x) xs)
  ≡⟨⟩
    y ⊗ (foldl _⊗_ e (x ∷ xs))
  ∎

-- 外延性の公理を用いた証明のための補題
lemma : ∀ {A : Set} → (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
lemma _⊗_ e ⊗-monoid [] =
  begin
    foldr _⊗_ e []
  ≡⟨⟩
    e
  ≡⟨⟩
    foldl _⊗_ e []
  ∎
lemma _⊗_ e ⊗-monoid (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ e xs)
  ≡⟨ cong (x ⊗_) (lemma _⊗_ e ⊗-monoid xs) ⟩
    x ⊗ (foldl _⊗_ e xs)
  ≡⟨ sym (foldl-monoid _⊗_ e ⊗-monoid xs x) ⟩
    foldl _⊗_ x xs
  ≡⟨ cong (λ e⊗x → foldl _⊗_ e⊗x xs) (sym (identityˡ ⊗-monoid x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎

-- _⊗_ と e がモノイドをなすとき、foldrとfoldlが等しくなることの証明
foldr-monoid-foldl : ∀ {A : Set} → (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e
  → foldr _⊗_ e ≡ foldl _⊗_ e
foldr-monoid-foldl _⊗_ e ⊗-monoid = extensionality (lemma _⊗_ e ⊗-monoid)
