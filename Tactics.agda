open import Order

open import Relation.Binary.PropositionalEquality

module Tactics {A} (preorder : Preorder A) where
  open Preorder preorder

  eq-⊑ : ∀ {a b} →
      a ≡ b →
      a ⊑ b
  eq-⊑ refl = ⊑-refl

  infixr 2 _⊢_⨾⟨_⟩_
  infix  3 _⊢_∎T
  infix  1 begin-tactics_

  -- Compose two tactics using function composition
  _⊢_⨾⟨_⟩_ : ∀ {a b} {c d} e r →
      (c ⊑ d → e ⊑ r) →
      (a ⊑ b → c ⊑ d) →
      (a ⊑ b → e ⊑ r)
  _⊢_⨾⟨_⟩_ e r f g x = f (g x)

  -- The "do nothing" tactic
  _⊢_∎T : ∀ a b →
      a ⊑ b → a ⊑ b
  _⊢_∎T _ _ x = x

  begin-tactics_ : ∀ {a b c : A} →
      (a ⊑ a → b ⊑ c) →
      b ⊑ c
  begin-tactics_ f = f ⊑-refl

  -- Given: a ⊢ b
  --
  -- Produces: a′ ⊢ b   --->   a ⊢ b
  rewrite⊢ : ∀ {a a′ b} →
      a ⊑ a′ →
      a′ ⊑ b →
      a ⊑ b
  rewrite⊢ p q = ⊑-trans p q

  -- Given: b ⊢ b′
  --
  -- Produces: a ⊢ b   --->   a ⊢ b′
  ⊢rewrite : ∀ {a b b′} →
      b ⊑ b′ →
      a ⊑ b →
      a ⊑ b′
  ⊢rewrite p q = ⊑-trans q p

  infix  1 begin_
  infix  3 _∎

  begin_ : ∀ {a b : A} →
      a ⊑ b →
      a ⊑ b
  begin_ p = p

  -- This is a convenient notation for applying ⊑-trans, similar to Agda's builtin _≡⟨_⟩_
  infixr 2 _⊑⟨_⟩_
  _⊑⟨_⟩_ : ∀ a {b c} →
      a ⊑ b →
      b ⊑ c →
      a ⊑ c
  _⊑⟨_⟩_ _ = ⊑-trans

  infixr 2 _⊑˘⟨_⟩_
  _⊑˘⟨_⟩_ : ∀ a {b c} →
      b ⊑ c →
      a ⊑ b →
      a ⊑ c
  _⊑˘⟨_⟩_ _ p q = ⊑-trans q p

  infixr 2 _⊑⟨⟩_
  _⊑⟨⟩_ : ∀ a {b} →
      a ⊑ b →
      a ⊑ b
  _⊑⟨⟩_ _ p = p

  _∎ : ∀ a →
      a ⊑ a
  _∎ _ = ⊑-refl
