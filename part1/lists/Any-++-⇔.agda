module Any-++-⇔ where

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import lists using (_⇔_; List; []; _∷_; _++_; Any; here; there; _∈_)

-- P が xs ++ ys で成り立つことと、 P が xs または ys で成り立つことは同値
Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
    { to = to xs ys
    ; from = from xs ys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P (xs ++ ys) → (Any P xs ⊎ Any P ys)
    to []       ys Pys                           = inj₂ Pys
    to (x ∷ xs) ys (here Px∷xs)                  = inj₁ (here Px∷xs)
    to (x ∷ xs) ys (there Pxs++ys) with to xs ys Pxs++ys
    ...                               | inj₁ Pxs = inj₁ (there Pxs)
    ...                               | inj₂ Pys = inj₂ Pys

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      Any P xs ⊎ Any P ys → Any P (xs ++ ys)
    from []       ys (inj₂ Pys)         = Pys
    from (x ∷ xs) ys (inj₁ (here Px))   = here Px
    from (x ∷ xs) ys (inj₁ (there Pxs)) = there (from xs ys (inj₁ Pxs))
    from (x ∷ xs) ys (inj₂ Pys)         = there (from xs ys (inj₂ Pys))

-- a が xs ++ ys に含まれていることと、 a が xs または ys に含まれていることは同値
∈-++-⇔ : ∀ {A : Set} {a : A} → (xs ys : List A) →
  (a ∈ xs ++ ys) ⇔ (a ∈ xs ⊎ a ∈ ys)
∈-++-⇔ xs ys = Any-++-⇔ xs ys
