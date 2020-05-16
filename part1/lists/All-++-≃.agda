module All-++-≃ where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import lists using (_≃_; List; []; _∷_; _++_; All)

-- All-++-⇔ の同型 (isomorphism) 版
All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ xs ys =
  record
    { to      = to xs ys
    ; from    = from xs ys
    ; from∘to = λ Pxs++ys → from∘to xs ys Pxs++ys
    ; to∘from = λ Pxs×Pys → to∘from xs ys Pxs×Pys
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P (xs ++ ys) → (All P xs × All P ys)
    to [] ys Pys = ⟨ [] , Pys ⟩
    to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
    ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

    from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
      All P xs × All P ys → All P (xs ++ ys)
    from [] ys ⟨ [] , Pys ⟩ = Pys
    from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ =  Px ∷ from xs ys ⟨ Pxs , Pys ⟩

    -- rewriteを使わない方法がわからない…
    from∘to : ∀ {A : Set} {P : A → Set} → (xs ys : List A) → (Pxs++ys : All P (xs ++ ys))
      → (from xs ys (to xs ys Pxs++ys)) ≡ Pxs++ys
    from∘to [] ys Pys = refl
    from∘to (x ∷ xs) ys (Px ∷ Pxs++ys) rewrite from∘to xs ys Pxs++ys = refl

    -- こっちも…
    to∘from : ∀ {A : Set} {P : A → Set} → (xs ys : List A) → (Pxs×Pys : All P xs × All P ys)
      → (to xs ys (from xs ys Pxs×Pys)) ≡ Pxs×Pys
    to∘from [] ys ⟨ [] , Pys ⟩ = refl
    to∘from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ rewrite to∘from xs ys ⟨ Pxs , Pys ⟩ = refl
