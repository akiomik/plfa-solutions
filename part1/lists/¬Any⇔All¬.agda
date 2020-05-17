module ¬Any⇔All¬ where

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Function using (_∘_)

open import lists using (_⇔_; List; []; _∷_; All; Any; here; there)

-- Any と All がド・モルガンの法則を満たすことの証明
¬Any⇔All¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → (¬_ ∘ Any P) xs ⇔ All (¬_ ∘ P) xs
¬Any⇔All¬ xs =
  record
    { to = to xs
    ; from = from xs
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

-- ¬All⇔Any¬ : ∀ {A : Set} {P : A → Set} (xs : List A)
--   → (¬_ ∘ All P) xs ⇔ Any (¬_ ∘ P) xs
-- ¬All⇔Any¬ xs =
--   record
--     { to = to xs
--     ; from = from xs
--     }
--   where
--     to : ∀ {A : Set} {P : A → Set} (xs : List A)
--       → (¬_ ∘ All P) xs → Any (¬_ ∘ P) xs
--     to []       ¬P[]   = {!!}
--     to (x ∷ xs) ¬Px∷xs = here λ Px → ¬Px∷xs (Px ∷ {!!})
--
--     from : ∀ {A : Set} {P : A → Set} (xs : List A)
--       → Any (¬_ ∘ P) xs → (¬_ ∘ All P) xs
--     from []       ()
--     from (x ∷ xs) (here ¬Px)   = λ{ (Px ∷ Pxs) → ¬Px Px }
--     from (x ∷ xs) (there ¬Pxs) = λ{ (Px ∷ Pxs) → from xs ¬Pxs Pxs }
