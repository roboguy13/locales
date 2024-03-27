{-# OPTIONS --prop #-}

module STLC
  where

infixr 21 _⇨_

data Type : Set where
  Boolean : Type
  _⇨_ : Type → Type → Type

data Context : Set where
  ∅ : Context
  _,,_ : Context → Type → Context

infix 10 _∋_

data _∋_ : Context → Type → Set where
  ∋-here : ∀ {Γ a} → Γ ,, a ∋ a
  ∋-there : ∀ {Γ a b} →
    Γ ∋ a →
    Γ ,, b ∋ a

_ : ∀ {Γ A B} → Γ ,, A ⇨ B ∋ A ⇨ B
_ = ∋-here

data Term : Context → Type → Set where
  V : ∀ {Γ a} → Γ ∋ a → Term Γ a
  true : ∀ {Γ} → Term Γ Boolean
  false : ∀ {Γ} → Term Γ Boolean
  cond : ∀ {Γ a} → Term Γ Boolean → Term Γ a → Term Γ a → Term Γ a
  _·_ : ∀ {Γ a b} → Term Γ (a ⇨ b) → Term Γ a → Term Γ b
  ƛ : ∀ {Γ a b} → Term (Γ ,, a) b → Term Γ (a ⇨ b)

open import Order
open import Frame

module Semantics {A} (frame : Frame A) where
  open Order.Frame frame
  open DistributiveLattice distr-lattice
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder
  open Locales frame
  open LatticeProps lattice

  ⟦_⟧ᵗ : Type → A
  ⟦ Boolean ⟧ᵗ = {!!}
  ⟦ a ⇨ b ⟧ᵗ = ⟦ a ⟧ᵗ ⇒ ⟦ b ⟧ᵗ

  ⟦_⟧ᶜ : Context → A
  ⟦ ∅ ⟧ᶜ = ⊤
  ⟦ Γ ,, a ⟧ᶜ = ⟦ Γ ⟧ᶜ ⊔ ⟦ a ⟧ᵗ

  -- ⟦_⟧ : ∀ {Γ a} → Term Γ a → A
  -- ⟦ V x ⟧ = {!!}
  -- ⟦ true ⟧ = {!!}
  -- ⟦ false ⟧ = {!!}
  -- ⟦ cond t t₁ t₂ ⟧ = {!!}
  -- ⟦ t · t₁ ⟧ = {!!}
  -- ⟦ ƛ t ⟧ = {!!}

