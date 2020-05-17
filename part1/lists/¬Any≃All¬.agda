module ¬Any≃All¬ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_)
open import Function using (_∘_)
open import Data.Empty using (⊥-elim)

open import lists using (_≃_; List; []; _∷_; All; Any; here; there)

postulate
  -- 外延性の公理
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- Any と All がド・モルガンの法則を満たすことの証明
¬Any≃All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ≃ All (¬_ ∘ P) xs
¬Any≃All¬ xs =
  record
    { to = to xs
    ; from = from xs
    ; from∘to = λ ¬Pxs → from∘to xs ¬Pxs
    ; to∘from = λ ¬Pxs → to∘from xs ¬Pxs
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → (¬_ ∘ Any P) xs → All (¬_ ∘ P) xs
    to []       ¬P[]   = []
    to (x ∷ xs) ¬Px∷xs = (λ Px → ¬Px∷xs (here Px)) ∷ (to xs λ Pxs → ¬Px∷xs (there Pxs))

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All (¬_ ∘ P) xs → (¬_ ∘ Any P) xs
    from []       []           = λ ()
    from (x ∷ xs) (¬Px ∷ ¬Pxs) = λ{ (here Px)   → ¬Px Px
                                  ; (there Pxs) → from xs ¬Pxs Pxs
                                  }

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬Pxs : (¬_ ∘ Any P) xs)
      → from xs (to xs ¬Pxs) ≡ ¬Pxs
    from∘to [] ¬P[] =
      begin
        from [] (to [] ¬P[])
      ≡⟨⟩
        from [] []
      ≡⟨ extensionality (λ ()) ⟩
        ¬P[]
      ∎
    from∘to (x ∷ xs) ¬Px∷xs =
      begin
        from (x ∷ xs) (to (x ∷ xs) ¬Px∷xs)
      ≡⟨⟩
        from (x ∷ xs) ((λ Px → ¬Px∷xs (here Px)) ∷ (to xs λ Pxs → ¬Px∷xs (there Pxs)))
      ≡⟨ extensionality (λ{ (here Px)   → refl
                          ; (there Pxs) → ⊥-elim (¬Px∷xs (there Pxs))
                          }) ⟩
        ¬Px∷xs
      ∎

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (¬Pxs : All (¬_ ∘ P) xs)
      → to xs (from xs ¬Pxs) ≡ ¬Pxs
    to∘from [] [] =
      begin
        to [] (from [] [])
      ≡⟨⟩
        []
      ∎
    to∘from (x ∷ xs) (¬Px ∷ ¬Pxs) =
      begin
        to (x ∷ xs) (from (x ∷ xs) (¬Px ∷ ¬Pxs))
      ≡⟨ cong (¬Px ∷_) (to∘from xs ¬Pxs) ⟩
        ¬Px ∷ ¬Pxs
      ∎
