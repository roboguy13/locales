--
-- Author: David Young
--
-- Description:
--   Working through some exercises in Stone Spaces. This also has a Coq-like tactic notation for writing proofs in an arbitrary Heyting algebra.
--

{-# OPTIONS --prop #-}

open import Data.Product
open import Agda.Primitive hiding (_⊔_)
open import Relation.Binary.PropositionalEquality hiding (preorder; Extensionality)

module FrameDefs
    where

open import Order

data Squash (A : Set) : Prop where
  squash : A → Squash A

squash-elim : ∀ (A : Set) (P : Prop) → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x

record Frame-morphism {A B : Set} (F-A : Frame A) (F-B : Frame B) : Set₁ where
  open Frame F-A renaming (Lub to A-Lub; distr-lattice to A-distr-lattice)
  open DistributiveLattice A-distr-lattice renaming (lattice to A-lattice)
  open Lattice A-lattice renaming (glb to A-glb)

  open Frame F-B renaming (Lub to B-Lub; distr-lattice to B-distr-lattice)
  open DistributiveLattice B-distr-lattice renaming (lattice to B-lattice)
  open Lattice B-lattice renaming (glb to B-glb)

  field
    act : A → B
    preserves-glb : ∀ {a b} →
      Squash (act (A-glb a b) ≡ B-glb (act a) (act b))

    preserves-Lub : ∀ {I : Set} {X : I → A} →
      Squash (act (A-Lub X) ≡ B-Lub (λ i → act (X i)))

Locale-morphism : {A B : Set} → Frame A → Frame B → Set₁
Locale-morphism F-A F-B = Frame-morphism F-B F-A

_F⇒_ = Frame-morphism
_L⇒_ = Locale-morphism

∥trans∥ : ∀ {A : Set} {x y z : A} → Squash (x ≡ y) → Squash (y ≡ z) → Squash (x ≡ z)
∥trans∥ (squash p) (squash q) = squash (trans p q)

∥cong∥ : ∀ {A : Set} {B : Set} (f : A → B) {x y : A} → Squash (x ≡ y) → Squash (f x ≡ f y)
∥cong∥ f (squash p) = squash (cong f p)

∥refl∥ : ∀ {A : Set} {x : A} → Squash (x ≡ x)
∥refl∥ = squash refl

_F∘_ : ∀ {A B C} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} →
  F-B F⇒ F-C →
  F-A F⇒ F-B →
  F-A F⇒ F-C
_F∘_ f g =
  record
    { act = λ x → Frame-morphism.act f (Frame-morphism.act g x)
    ; preserves-glb = λ {a} {b} → ∥trans∥ (∥cong∥ (Frame-morphism.act f) (Frame-morphism.preserves-glb g)) (Frame-morphism.preserves-glb f)
    ; preserves-Lub = λ {I} {X} → ∥trans∥ (∥cong∥ (Frame-morphism.act f) (Frame-morphism.preserves-Lub g)) (Frame-morphism.preserves-Lub f)
    }

_L∘_ : ∀ {A B C} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} →
  F-B L⇒ F-C →
  F-A L⇒ F-B →
  F-A L⇒ F-C
_L∘_ f g = g F∘ f

id-F : ∀ {A} {F-A : Frame A} → F-A F⇒ F-A
id-F =
  record
    { act = λ z → z
    ; preserves-glb = ∥refl∥
    ; preserves-Lub = ∥refl∥
    }

F∘-assoc : ∀ {A B C D} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} {F-D : Frame D} →
  {f : F-C F⇒ F-D} →
  {g : F-B F⇒ F-C} →
  {h : F-A F⇒ F-B} →
  ((f F∘ g) F∘ h) ≡ (f F∘ (g F∘ h))
F∘-assoc {f = f} {g = g} {h = h} = refl

Frame-morphism-η : ∀ {A B} {F-A : Frame A} {F-B : Frame B} {m m′ : F-A F⇒ F-B} →
  Frame-morphism.act m ≡ Frame-morphism.act m′ →
  m ≡ m′
Frame-morphism-η refl = refl

module LatticeProps {ℓ} {A : Set ℓ} (lattice : Lattice A) where

  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder

  _⊔_ = lub
  _⊓_ = glb

  lub-idem : ∀ {a} →
    lub a a ≡ a
  lub-idem {a} = antisym (proj₂ lub-is-lub a (⊑-refl , ⊑-refl)) (proj₂ lub-is-upper-bound)

  lub-monotone : ∀ {a a′ b b′} →
    a ⊑ a′ →
    b ⊑ b′ →
    lub a b ⊑ lub a′ b′
  lub-monotone {a} {a′} {b} {b′} a⊑a′ b⊑b′ = universal lub-upper-bound
    where
      universal : ∀ {z} → is-upper-bound preorder a b z → lub a b ⊑ z
      universal {z} = proj₂ lub-is-lub z

      lub-upper-bound :
        a ⊑ lub a′ b′
          ×
        b ⊑ lub a′ b′
      lub-upper-bound = ⊑-trans a⊑a′ (proj₁ lub-is-upper-bound) ,
                        ⊑-trans b⊑b′ (proj₂ lub-is-upper-bound)

  lub-comm : ∀ {a b} →
    lub a b ≡ lub b a
  lub-comm {a} {b} = antisym (universal-lub-a-b (a⊑lub-b-a , b⊑lub-b-a)) (universal-lub-b-a (b⊑lub-a-b , a⊑lub-a-b))
    where
      universal-lub-a-b : ∀ {z} → is-upper-bound preorder a b z → lub a b ⊑ z
      universal-lub-a-b {z} = proj₂ lub-is-lub z

      universal-lub-b-a : ∀ {z} → is-upper-bound preorder b a z → lub b a ⊑ z
      universal-lub-b-a {z} = proj₂ lub-is-lub z

      a⊑lub-b-a : a ⊑ lub b a
      a⊑lub-b-a = proj₂ lub-is-upper-bound

      b⊑lub-b-a : b ⊑ lub b a
      b⊑lub-b-a = proj₁ lub-is-upper-bound

      a⊑lub-a-b : a ⊑ lub a b
      a⊑lub-a-b = proj₁ lub-is-upper-bound

      b⊑lub-a-b : b ⊑ lub a b
      b⊑lub-a-b = proj₂ lub-is-upper-bound

  lub-assoc : ∀ {a b c} →
    lub a (lub b c) ≡ lub (lub a b) c
  lub-assoc {a} {b} {c} = antisym (universal-1 p) (universal-2 q)
    where
      universal-1 : ∀ {z} → is-upper-bound preorder a (lub b c) z → lub a (lub b c) ⊑ z
      universal-1 {z} = proj₂ lub-is-lub z

      universal-2 : ∀ {z} → is-upper-bound preorder (lub a b) c z → lub (lub a b) c ⊑ z
      universal-2 {z} = proj₂ lub-is-lub z

      universal-3 : ∀ {z} → is-upper-bound preorder a b z → lub a b ⊑ z
      universal-3 {z} = proj₂ lub-is-lub z

      universal-4 : ∀ {z} → is-upper-bound preorder b c z → lub b c ⊑ z
      universal-4 {z} = proj₂ lub-is-lub z

      p0 : is-upper-bound preorder b c (lub (lub a b) c)
      p0 =
        let x , y = lub-is-upper-bound {lub a b} {c}
            w , r = lub-is-upper-bound {a} {b}
        in
        ⊑-trans r x , y

      p : is-upper-bound preorder a (lub b c) (lub (lub a b) c)
      p =
        let x , _ = lub-is-upper-bound {lub a b} {c}
        in
        ⊑-trans (proj₁ lub-is-upper-bound) x , universal-4 p0


      q0 : is-upper-bound preorder a b (lub a (lub b c))
      q0 =
        let x , y = lub-is-upper-bound {a} {lub b c}
            w , r = lub-is-upper-bound {b} {c}
        in
        proj₁ lub-is-upper-bound , ⊑-trans w y

      q : is-upper-bound preorder (lub a b) c (lub a (lub b c))
      q =
        let _ , x = lub-is-upper-bound {a} {lub b c}
            _ , y = lub-is-upper-bound {b} {c}
        in
        universal-3 q0 , ⊑-trans y x

  absorb-1 : ∀ {a b} → lub a (glb a b) ≡ a
  absorb-1 {a} {b} =
    antisym (⊑-trans p1 (subst (λ z → z ⊑ a) (sym lub-idem) ⊑-refl))
            (proj₁ lub-is-upper-bound)
    where
      p : glb a b ⊑ a
      p = proj₁ glb-is-lower-bound

      p1 : lub a (glb a b) ⊑ lub a a
      p1 = lub-monotone ⊑-refl p


module DualLatticeProps {ℓ} {A : Set ℓ} (lattice : Lattice A) where
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder

  Op : Preorder A
  Op =
    record { _⊑_ = λ a b → b ⊑ a ; ⊑-refl = ⊑-refl ; ⊑-trans = λ p q → ⊑-trans q p }

  Op-PartialOrder : PartialOrder A
  Op-PartialOrder = record { preorder = Op ; antisym = λ a b → antisym b a }

  Op-Lattice : Lattice A
  Op-Lattice = record { porder = Op-PartialOrder ; lub-exists = glb-exists ; glb-exists = lub-exists }

  open LatticeProps -- (Op-Lattice)

  glb-op : ∀ {a b} →
    glb a b ≡ Lattice.lub Op-Lattice a b
  glb-op = refl

  glb-idem : ∀ {a} →
    glb a a ≡ a
  glb-idem = lub-idem Op-Lattice

  glb-monotone : ∀ {a a′ b b′} →
    a ⊑ a′ →
    b ⊑ b′ →
    glb a b ⊑ glb a′ b′
  glb-monotone = lub-monotone Op-Lattice

  glb-comm : ∀ {a b} →
    glb a b ≡ glb b a
  glb-comm = lub-comm Op-Lattice

  glb-assoc : ∀ {a b c} →
    glb a (glb b c) ≡ glb (glb a b) c
  glb-assoc {a} {b} {c} = lub-assoc Op-Lattice

  absorb-2 : ∀ {a b} → glb a (lub a b) ≡ a
  absorb-2 = absorb-1 Op-Lattice

  lub-glb⊑ : ∀ {a b c} →
    lub a (glb b c) ⊑ glb (lub a b) (lub a c)
  lub-glb⊑ {a} {b} {c} = universal upper-bound
    where
      universal : ∀ {z} → is-upper-bound Op (lub a b) (lub a c) z → z ⊑ glb (lub a b) (lub a c)
      universal {z} = proj₂ glb-is-glb z

      glb-b-c⊑b : glb b c ⊑ b
      glb-b-c⊑b =
        let (x , _) , _ = glb-is-glb {b} {c}
        in
        x

      glb-b-c⊑c : glb b c ⊑ c
      glb-b-c⊑c =
        let (_ , x) , _ = glb-is-glb {b} {c}
        in
        x

      upper-bound : is-upper-bound Op (lub a b) (lub a c) (lub a (glb b c))
      upper-bound = lub-monotone lattice ⊑-refl glb-b-c⊑b , lub-monotone lattice ⊑-refl glb-b-c⊑c

  glb-a-b-a : ∀ {a b} →
    glb (glb a b) a ≡ glb a b
  glb-a-b-a {a} {b} =
    trans (sym glb-assoc) (trans (cong (glb a) glb-comm) (trans glb-assoc (cong₂ glb glb-idem refl)))

