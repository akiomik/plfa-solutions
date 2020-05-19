module Any-∃ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import lists using (_≃_; List; []; _∷_; Any; here; there; _∈_)

-- リストxsに対するAnyと存在量化子∃が同型であることの証明
Any-∃ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs =
  record
    { to      = to xs
    ; from    = from xs
    ; from∘to = λ Pxs → from∘to xs Pxs
    ; to∘from = λ ∃x∈xsPx → to∘from xs ∃x∈xsPx
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → Any P xs → ∃[ x ] (x ∈ xs × P x)
    to []       ()
    to (x ∷ xs) (here Px)                                  = ⟨ x ,  ⟨ here refl ,   Px ⟩ ⟩
    to (x ∷ xs) (there Pxs) with to xs Pxs
    ...                        | (⟨ x′ , ⟨ x'∈xs , Px ⟩ ⟩) = ⟨ x′ , ⟨ there x'∈xs , Px ⟩ ⟩

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → ∃[ x ] (x ∈ xs × P x) → Any P xs
    from []       ()
    from (x ∷ xs) (⟨ x , ⟨ (here refl) ,  Px ⟩ ⟩) = here Px
    from (x ∷ xs) (⟨ y , ⟨ (there y∈xs) , Py ⟩ ⟩) = there (from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩)

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (Pxs : Any P xs)
      → (from xs (to xs Pxs)) ≡ Pxs
    from∘to [] ()
    from∘to (x ∷ xs) (here Px) =
      begin
        from (x ∷ xs) (to (x ∷ xs) (here Px))
      ≡⟨⟩
        from (x ∷ xs) ⟨ x , ⟨ here refl , Px ⟩ ⟩
      ≡⟨⟩
        here Px
      ∎
    from∘to (x ∷ xs) (there Pxs) =
      begin
        from (x ∷ xs) (to (x ∷ xs) (there Pxs))
      ≡⟨ cong ( λ Pxs′ → there Pxs′) (from∘to xs Pxs) ⟩
        there Pxs
      ∎

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (∃x∈xs×Px : ∃[ x ] (x ∈ xs × P x))
      → (to xs (from xs ∃x∈xs×Px)) ≡ ∃x∈xs×Px
    to∘from [] ()
    to∘from (x ∷ xs) (⟨ x , ⟨ here refl , Px ⟩ ⟩) =
      begin
        to (x ∷ xs) (from (x ∷ xs) ⟨ x , ⟨ here refl , Px ⟩ ⟩)
      ≡⟨⟩
        to (x ∷ xs) (here Px)
      ≡⟨⟩
        ⟨ x , ⟨ here refl , Px ⟩ ⟩
      ∎
    to∘from (x ∷ xs) (⟨ y , ⟨ there y∈xs , Py ⟩ ⟩) =
      begin
        to (x ∷ xs) (from (x ∷ xs) ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩)
      ≡⟨ cong (λ (⟨ y , ⟨ y∈xs , Py ⟩ ⟩) → ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩) (to∘from xs ⟨ y , ⟨ y∈xs , Py ⟩ ⟩) ⟩
        ⟨ y , ⟨ there y∈xs , Py ⟩ ⟩
      ∎
