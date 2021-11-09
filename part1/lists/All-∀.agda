module All-∀ where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import lists using (_≃_; List; []; _∷_; All; here; there; _∈_)

postulate
  -- 外延性の公理
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
  extensionality′ : ∀ {A : Set} {B C : A → Set} {f g : ∀ {x : A} → B x → C x}
    → (∀ {x : A} (Bx : B x) → f {x} Bx ≡ g {x} Bx)
      ---------------------------------------
    → (λ {x} → f {x}) ≡ (λ {x} → g {x})

-- 命題 P がリスト xs のすべてで成り立つことと、
-- リスト xs の任意の元 x で 命題 P が成り立つことが同型である証明
All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A)
  → All P xs ≃ (∀ {x : A} → x ∈ xs → P x)
All-∀ xs =
  record
    { to      = to xs
    ; from    = from xs
    ; from∘to = λ Pxs → from∘to xs Pxs
    ; to∘from = λ x∈xs→Px → to∘from xs x∈xs→Px
    }
  where
    to : ∀ {A : Set} {P : A → Set} (xs : List A)
      → All P xs → (∀ {x} → x ∈ xs → P x)
    to []       _          = λ ()
    to (x ∷ xs) (Px ∷ Pxs) = λ{ (here refl) → Px
                              ; (there x∈xs) → to xs Pxs x∈xs }

    from : ∀ {A : Set} {P : A → Set} (xs : List A)
      → (∀ {x} → x ∈ xs → P x) → All P xs
    from []       _       = []
    from (x ∷ xs) x∈xs→Px = x∈xs→Px (here refl) ∷ from xs (λ x∈xs → x∈xs→Px (there x∈xs))

    from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) → (Pxs : All P xs)
      → (from xs (to xs Pxs)) ≡ Pxs
    from∘to []       []         = refl
    from∘to (x ∷ xs) (Px ∷ Pxs) =
      begin
        from (x ∷ xs) (to (x ∷ xs) (Px ∷ Pxs))
      ≡⟨ cong (Px ∷_) (from∘to xs Pxs) ⟩
        Px ∷ Pxs
      ∎

    to∘from : ∀ {A : Set} {P : A → Set} (xs : List A) → (x∈xs : ∀ {x} → x ∈ xs → P x)
      → (λ {x} → to xs (from xs x∈xs) {x}) ≡ (λ {x} → x∈xs {x})
    to∘from [] x∈xs→Px = extensionality′ λ()
    --  begin
    --    (λ {x} → to [] (from [] x∈xs→Px) {x})
    --  ≡⟨⟩
    --    (λ {x} → to [] [] {x})
    --  ≡⟨⟩
    --    (λ {x} → (λ ()) x)
    --  ≡⟨ cong (λ x → λ {x} → λ()) (extensionality′ λ()) ⟩
    --    (λ {x} → x∈xs→Px {x})
    --  ∎
    to∘from (x ∷ xs) y∈x∷xs→Py =
      begin
        (λ {y} → to (x ∷ xs) (from (x ∷ xs) y∈x∷xs→Py) {y})
      ≡⟨⟩
        (λ {y} → to (x ∷ xs) (y∈x∷xs→Py (here refl) ∷ from xs (λ y∈xs → y∈x∷xs→Py (there y∈xs))) {y})
     ≡⟨ extensionality′ (λ{ (here refl) → refl
                          ; (there y∈xs) → cong (λ y∈xs → {!!}) (to∘from xs ({!!})) }) ⟩
        (λ {y} → y∈x∷xs→Py {y})
      ∎
