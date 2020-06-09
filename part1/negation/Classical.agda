module Classical where

open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)

open import Negation using (¬_)

-- 排中律 → 二重否定の除去
em-→-¬¬-elim :
    (∀ {A : Set} → A ⊎ ¬ A)
    -------------------------
  → (∀ {A : Set} → ¬ ¬ A → A)
em-→-¬¬-elim a⊎¬a ¬¬a with a⊎¬a
...                      | inj₁ a  = a
...                      | inj₂ ¬a = ⊥-elim (¬¬a ¬a)

-- 排中律 → パースの法則
em-→-peirce :
    (∀ {A : Set} → A ⊎ ¬ A)
    -----------------------------------
  → (∀ {A B : Set} → ((A → B) → A) → A)
em-→-peirce a⊎¬a [a→b]→a with a⊎¬a
...                         | inj₁ a  = a
...                         | inj₂ ¬a = [a→b]→a (λ a → ⊥-elim (¬a a))

-- 排中律 → 直和としての含意
em-→-iad :
    (∀ {A : Set} → A ⊎ ¬ A)
    -------------------------------------
  → (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
em-→-iad a⊎¬a a→b with a⊎¬a
...                  | inj₁ a  = inj₂ (a→b a)
...                  | inj₂ ¬a = inj₁ ¬a

-- 排中律 → ド・モルガンの法則
em-→-demorgan :
    (∀ {A : Set} → A ⊎ ¬ A)
    ---------------------------------------
  → (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
em-→-demorgan a⊎¬a {A} {B} ¬[¬a×¬b] with a⊎¬a {A} | a⊎¬a {B}
...                                    | inj₁ a   | _        = inj₁ a
...                                    | inj₂ ¬a  | inj₁ b   = inj₂ b
...                                    | inj₂ ¬a  | inj₂ ¬b  = ⊥-elim (¬[¬a×¬b] ⟨ ¬a , ¬b ⟩)

-- 二重否定の除去 → 排中律
-- (¬¬ A → A) の A を (A ⊎ ¬ A) と見なす
-- ¬¬ (A ⊎ ¬ A) → (A ⊎ ¬ A)
¬¬-elim-→-em :
    (∀ {A : Set} → ¬ ¬ A → A)
    -------------------------
  → (∀ {A : Set} → A ⊎ ¬ A)
¬¬-elim-→-em ¬¬[a⊎¬a]→[a⊎¬a] = ¬¬[a⊎¬a]→[a⊎¬a] (λ ¬[a⊎¬a] → ¬[a⊎¬a] (inj₂ (λ a → ¬[a⊎¬a] (inj₁ a))))

-- 二重否定の除去 → パースの法則
¬¬-elim-→-peirce :
    (∀ {A : Set} → ¬ ¬ A → A)
    -----------------------------------
  → (∀ {A B : Set} → ((A → B) → A) → A)
¬¬-elim-→-peirce ¬¬a→a [a→b]→a = ¬¬a→a (λ ¬a → ¬a ([a→b]→a (λ a → ⊥-elim (¬a a))))

-- 二重否定の除去 → 直和としての含意
-- (¬¬ A → A) の A を (¬ A ⊎ B) と見なす
-- ¬¬ (¬ A ⊎ B) → (¬ A ⊎ B)
¬¬-elim-→-iad :
    (∀ {A : Set} → ¬ ¬ A → A)
    -------------------------------------
  → (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
¬¬-elim-→-iad ¬¬[¬a⊎b]→[¬a⊎b] a→b = ¬¬[¬a⊎b]→[¬a⊎b] (λ ¬[¬a⊎b] → ¬[¬a⊎b] (inj₁ (λ a → ¬[¬a⊎b] (inj₂ (a→b a)))))

-- 二重否定の除去 → ド・モルガンの法則
-- (¬¬ A → A) の A を (A ⊎ B) と見なす
-- ¬¬ (A ⊎ B) → (A ⊎ B)
¬¬-elim-→-demorgan :
    (∀ {A : Set} → ¬ ¬ A → A)
    ---------------------------------------
  → (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
¬¬-elim-→-demorgan ¬¬[a⊎b]→[a⊎b] ¬[¬a×¬b] = ¬¬[a⊎b]→[a⊎b] (λ ¬[a⊎b] → ¬[¬a×¬b] ⟨ (λ a → ¬[a⊎b] (inj₁ a)) , (λ b → ¬[a⊎b] (inj₂ b)) ⟩)

-- パースの法則 → 排中律
-- ((A → B) → A) → A) の A を (A ⊎ ¬ A) と見なす
-- ((((A ⊎ ¬ A) → B) → (A ⊎ ¬ A)) → (A ⊎ ¬ A))
peirce-→-em :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → (∀ {A : Set} → A ⊎ ¬ A)
peirce-→-em [[[a⊎¬a]→b]→[a⊎¬a]]→[a⊎¬a] = [[[a⊎¬a]→b]→[a⊎¬a]]→[a⊎¬a] (λ [a⊎¬a]→b → inj₂ (λ a → [a⊎¬a]→b (inj₁ a)))

-- パースの法則 → 二重否定の除去
-- ((A → B) → A) → A) の A を (¬¬ A → A) と見なす
-- (((¬¬ A → A) → B) → (¬¬ A → A)) → (¬¬ A → A))
peirce-→-¬¬-elim :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -----------------------------------
  → (∀ {A : Set} → ¬ ¬ A → A)
peirce-→-¬¬-elim [[[¬¬a→a]→b]→[¬¬a→a]]→[¬¬a→a] = [[[¬¬a→a]→b]→[¬¬a→a]]→[¬¬a→a] (λ [¬¬a→a]→b → (λ ¬¬a → ⊥-elim (¬¬a (λ a → [¬¬a→a]→b (λ ¬¬a → a)))))

-- パースの法則 → 直和としての含意
-- ((A → B) → A) → A の A を ¬ A ⊎ B, B を ⊥ と見なす
-- (¬ (¬ A ⊎ B)) → (¬ A ⊎ B) → (¬ A ⊎ B)
peirce-→-iad :
    (∀ {A B : Set} → ((A → B) → A) → A)
    -------------------------------------
  → (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
peirce-→-iad [¬[¬a⊎b]→[¬a⊎b]]→[¬a⊎b] a→b = [¬[¬a⊎b]→[¬a⊎b]]→[¬a⊎b] (λ ¬[¬a⊎b] → inj₁ (λ a → ¬[¬a⊎b] (inj₂ (a→b a))))

-- パースの法則 → ド・モルガンの法則
-- ((A → B) → A) → A) の A を (A ⊎ B), B を ⊥ と見なす
-- (¬ (A ⊎ B) → (A ⊎ B)) → (A ⊎ B)
peirce-→-demorgan :
    (∀ {A B : Set} → ((A → B) → A) → A)
    ---------------------------------------
  → (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
peirce-→-demorgan ¬[a⊎b]→[a⊎b]→[a⊎b] ¬[¬a×¬b] = ¬[a⊎b]→[a⊎b]→[a⊎b] (λ ¬[a⊎b] → ⊥-elim (¬[¬a×¬b] ⟨ (λ a → ¬[a⊎b] (inj₁ a)) , (λ b → ¬[a⊎b] (inj₂ b)) ⟩))

-- 直和としての含意 → 排中律
-- (A → B) → ¬ A ⊎ B は B を A と見ることで排中律と同じように扱える
-- (A → A) → ¬ A ⊎ A
iad-→-em :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → (∀ {A : Set} → A ⊎ ¬ A)
iad-→-em [a→b]→¬a⊎b with [a→b]→¬a⊎b (λ a → a)
...                    | inj₁ ¬a              = inj₂ ¬a
...                    | inj₂ a               = inj₁ a

-- 直和としての含意 → 二重否定の除去
iad-→-¬¬-elim :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → (∀ {A : Set} → ¬ ¬ A → A)
iad-→-¬¬-elim [a→b]→¬a⊎b with [a→b]→¬a⊎b (λ a → a)
...                         | inj₁ ¬a              = λ ¬¬a → ⊥-elim (¬¬a ¬a)
...                         | inj₂ a               = λ ¬¬a → a

-- 直和としての含意 → パースの法則
iad-→-peirce :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    -----------------------------------
  → (∀ {A B : Set} → ((A → B) → A) → A)
iad-→-peirce [a→b]→¬a⊎b [a→b]→a with [a→b]→¬a⊎b (λ a → a)
...                                | inj₁ ¬a              = [a→b]→a (λ a → ⊥-elim (¬a a))
...                                | inj₂ a               = a


-- 直和としての含意 → ド・モルガンの法則
iad-→-demorgan :
    (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
    ---------------------------------------
  → (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
iad-→-demorgan [a→b]→¬a⊎b {A} {B} ¬[¬a×¬b] with [a→b]→¬a⊎b {A} {A} (λ a → a) | [a→b]→¬a⊎b {B} {B} (λ b → b)
...                                           | inj₁ ¬a                      | inj₁ ¬b                      = ⊥-elim (¬[¬a×¬b] ⟨ ¬a , ¬b ⟩)
...                                           | inj₂ a                       | _                            = inj₁ a
...                                           | inj₁ ¬a                      | inj₂ b                       = inj₂ b

-- ド・モルガンの法則 → 排中律
demorgan-→-em :
    (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
    ---------------------------------------
  → (∀ {A : Set} → A ⊎ ¬ A)
demorgan-→-em ¬[¬a×¬b]→a⊎b = ¬[¬a×¬b]→a⊎b (λ{ (⟨ ¬a , ¬¬a ⟩) → ¬¬a ¬a })

-- ド・モルガンの法則 → 二重否定の除去
-- (¬ (¬ A × ¬ B) → A ⊎ B) の B を A と見なす
-- ¬ (¬ A × ¬ A) → A ⊎ A
demorgan-→-¬¬-elim :
    (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
    ---------------------------------------
  → (∀ {A : Set} → ¬ ¬ A → A)
demorgan-→-¬¬-elim ¬[¬a×¬b]→a⊎b {A} ¬¬a with ¬[¬a×¬b]→a⊎b {A} {A} λ{ (⟨ ¬a , ¬b ⟩) → ¬¬a ¬a }
...                                        | inj₁ a                                           = a
...                                        | inj₂ a                                           = a

-- ド・モルガンの法則 → パースの法則
-- (¬ (¬ A × ¬ B) → A ⊎ B) の B を A と見なす
-- ¬ (¬ A × ¬ A) → A ⊎ A
demorgan-→-peirce :
    (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
    ---------------------------------------
  → (∀ {A B : Set} → ((A → B) → A) → A)
demorgan-→-peirce ¬[¬¬a×¬b]→¬a⊎b {A} {B} [a→b]→a with ¬[¬¬a×¬b]→¬a⊎b {A} {A} λ{ (⟨ ¬a , ¬b ⟩) → ¬a ([a→b]→a (λ a → ⊥-elim (¬a a))) }
...                                                 | inj₁ a                                                                         = a
...                                                 | inj₂ a                                                                         = a

-- ド・モルガンの法則 → 直和としての含意
-- (¬ (¬ A × ¬ B) → A ⊎ B) の A を ¬A と見なす
-- ¬ (¬¬ A × ¬ B) → ¬ A ⊎ B
demorgan-→-iad :
    (∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B)
    ---------------------------------------
  → (∀ {A B : Set} → (A → B) → ¬ A ⊎ B)
demorgan-→-iad ¬[¬¬a×¬b]→¬a⊎b a→b = ¬[¬¬a×¬b]→¬a⊎b (λ (⟨ ¬¬a , ¬b ⟩) → ¬¬a (λ a → ¬b (a→b a)))
