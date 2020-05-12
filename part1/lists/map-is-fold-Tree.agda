module map-is-fold-Tree where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning

open import map-Tree using (Tree; leaf; node; map-Tree)
open import fold-Tree using (fold-Tree)

postulate
  -- 外延性の公理
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- 外延性の公理を利用した証明のための補題
lemma : ∀ {A B C D : Set} → (f : A → C) → (g : B → D) → (tree : Tree A B)
  → map-Tree f g tree ≡ fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) tree
lemma f g (leaf a) =
  begin
    map-Tree f g (leaf a)
  ≡⟨⟩
    leaf (f a)
  ≡⟨⟩
    fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) (leaf a)
  ∎
lemma f g (node treeˡ b treeʳ) =
  begin
    map-Tree f g (node treeˡ b treeʳ)
  ≡⟨⟩
    node (map-Tree f g treeˡ) (g b) (map-Tree f g treeʳ)
  ≡⟨ cong (λ treeʳ′ → node (map-Tree f g treeˡ) (g b) treeʳ′) (lemma f g treeʳ) ⟩
    node (map-Tree f g treeˡ)
         (g b)
         (fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) treeʳ)
  ≡⟨ cong (λ treeˡ′ → node treeˡ′
                           (g b)
                           (fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) treeʳ))
          (lemma f g treeˡ) ⟩
    node (fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) treeˡ)
         (g b)
         (fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) treeʳ)
  ≡⟨⟩
    fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ) (node treeˡ b treeʳ)
  ∎

-- Treeのmapが畳み込みで表現できることの証明
map-is-fold-Tree : ∀ {A B C D : Set} → (f : A → C) → (g : B → D)
  → map-Tree f g ≡ fold-Tree (λ a → leaf (f a)) (λ treeˡ b treeʳ → node treeˡ (g b) treeʳ)
map-is-fold-Tree f g = extensionality (lemma f g)
