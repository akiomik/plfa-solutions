module Any? where

open import Relation.Nullary using (¬_; Dec; yes; no)

open import lists using ([]; _∷_; Any; here; there; Decidable)

-- All?のAny版
Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? []                                = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
...                 | yes Px | _          = yes (here Px)
...                 | no _   | yes Pxs    = yes (there Pxs)
...                 | no ¬Px | no ¬Pxs    = no λ{ (here Px)   → ¬Px Px
                                                ; (there Pxs) → ¬Pxs Pxs }
