module map-Tree where

-- ツリー
data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

-- ツリーのmap
map-Tree : ∀ {A B C D : Set} → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf a)             = leaf (f a)
map-Tree f g (node treeˡ b treeʳ) = node (map-Tree f g treeˡ) (g b) (map-Tree f g treeʳ)
