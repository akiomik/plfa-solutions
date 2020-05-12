module fold-Tree where

open import map-Tree using (Tree; leaf; node)

fold-Tree : ∀ {A B C : Set} → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f _ (leaf a)             = f a
fold-Tree f g (node treeˡ b treeʳ) = g (fold-Tree f g treeˡ) b (fold-Tree f g treeʳ)
