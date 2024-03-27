{-# OPTIONS --prop #-}

open import Order
open import FrameDefs

open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (preorder)

module Tactics {A} (frame : Frame A) where
  open Frame frame

  open DistributiveLattice distr-lattice
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder
  open LatticeProps lattice
  open DualLatticeProps lattice
  open Implication frame

  -- module Tactics {A : Set ℓ} (porder : PartialOrder A) where
  --   open PartialOrder porder
  --   open Preorder preorder
  
  eq-⊑ : ∀ {a b} →
      a ≡ b →
      a ⊑ b
  eq-⊑ refl = ⊑-refl
  
  --   infixr 2 _⊢_⨾⟨_⟩_
  --   infix  3 _⊢_∎T
  --   infix  1 begin-tactics_
  
  --   _⊢_⨾⟨_⟩_ : ∀ {a b} {c d} e r →
  --       (c ⊑ d → e ⊑ r) →
  --       (a ⊑ b → c ⊑ d) →
  --       (a ⊑ b → e ⊑ r)
  --   _⊢_⨾⟨_⟩_ e r f g x = f (g x)
  
  --   _⊢_∎T : ∀ a b →
  --       a ⊑ b → a ⊑ b
  --   _⊢_∎T _ _ x = x
  
  --   begin-tactics_ : ∀ {a b c : A} →
  --       (a ⊑ a → b ⊑ c) →
  --       b ⊑ c
  --   begin-tactics_ f = f ⊑-refl
  
  --   -- Given: a ⊢ b
  --   --
  --   -- Produces: a′ ⊢ b   --->   a ⊢ b
  --   rewrite⊢ : ∀ {a a′ b} →
  --       a ⊑ a′ →
  --       a′ ⊑ b →
  --       a ⊑ b
  --   rewrite⊢ p q = ⊑-trans p q
  
  --   -- Given: b ⊢ b′
  --   --
  --   -- Produces: a ⊢ b   --->   a ⊢ b′
  --   ⊢rewrite : ∀ {a b b′} →
  --       b ⊑ b′ →
  --       a ⊑ b →
  --       a ⊑ b′
  --   ⊢rewrite p q = ⊑-trans q p
  
  
  --   infix  1 begin_
  --   infix  3 _∎
  
  --   begin_ : ∀ {a b : A} →
  --       a ⊑ b →
  --       a ⊑ b
  --   begin_ p = p
  
  --   infixr 2 _⊑⟨_⟩_
  --   _⊑⟨_⟩_ : ∀ a {b c} →
  --       a ⊑ b →
  --       b ⊑ c →
  --       a ⊑ c
  --   _⊑⟨_⟩_ _ = ⊑-trans
  
  --   infixr 2 _⊑˘⟨_⟩_
  --   _⊑˘⟨_⟩_ : ∀ a {b c} →
  --       b ⊑ c →
  --       a ⊑ b →
  --       a ⊑ c
  --   _⊑˘⟨_⟩_ _ p q = ⊑-trans q p
  
  --   infixr 2 _⊑⟨⟩_
  --   _⊑⟨⟩_ : ∀ a {b} →
  --       a ⊑ b →
  --       a ⊑ b
  
  --   _⊑⟨⟩_ _ p = p
  
  --   _∎ : ∀ a →
  --       a ⊑ a
  --   _∎ _ = ⊑-refl

  app-1 : ∀ {a b} →
    glb a (a ⇒ b) ⊑ b
  app-1 {a} {b} rewrite Lub-distr-glb {∃[ x ] (glb x a ⊑ b)} {a} (λ i → proj₁ i) =
    proj₂ Lub-is-Lub b λ {i} → let j , k = i in ⊑-trans (eq-⊑ (glb-comm {a} {j})) k

  app-1′ : ∀ {a b} →
    glb (a ⇒ b) a ⊑ b
  app-1′ = ⊑-trans (eq-⊑ glb-comm) app-1

  glb-⊤ : ∀ {a} →
    glb a ⊤ ≡ a
  glb-⊤ {a} = antisym (proj₁ glb-is-lower-bound) (proj₂ glb-is-glb a (⊑-refl , ⊤-is-top))

  module FrameTactics where
    -- z ⊓ (a ⇒ b) ⊑ b   --->   z ⊑ a
    apply : ∀ {a b z} →
        z ⊑ a →
        glb z (a ⇒ b) ⊑ b
    apply p = ⊑-trans (glb-monotone p ⊑-refl) app-1

    -- a ⊢ b   --->   ⊢ a ⇒ b
    intro : ∀ {a b} →
        a ⊑ b →
        ⊤ ⊑ (a ⇒ b)
    intro p = ⇒⊑ (⊑-trans (proj₂ glb-is-lower-bound) p)

    -- a ⊓ b ⊑ c   --->   a ⊑ b ⇒ c
    intro-glb : ∀ {a b c} →
        glb a b ⊑ c →
        a ⊑ (b ⇒ c)
    intro-glb = ⇒⊑

    -- ⊢ a ⇒ b   --->   a ⊢ b
    generalize : ∀ {a b} →
        ⊤ ⊑ (a ⇒ b) →
        a ⊑ b
    generalize p = ⊑-trans (eq-⊑ (sym glb-⊤)) (⊑-trans (eq-⊑ glb-comm) (⊑⇒ p))

