--
-- Author: David Young
--
-- Description:
--   Working through some exercises in Stone Spaces. This also has a Coq-like tactic notation for writing proofs in an arbitrary Heyting algebra.
--

open import Data.Product
open import Agda.Primitive hiding (_⊔_)
open import Relation.Binary.PropositionalEquality hiding (preorder)

module Order
    where

record Preorder (A : Set) : Set₁ where
  field
    _⊑_ : A → A → Set
    ⊑-refl : ∀ {x} → x ⊑ x
    ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z

is-least : ∀ {A} → Preorder A → (A → Set) → A → Set
is-least pre P z =
  P z × (∀ w → P w → z ⊑ w)
  where
    open Preorder pre

is-greatest : ∀ {A} → Preorder A → (A → Set) → A → Set
is-greatest pre P z =
  P z × (∀ w → P w → w ⊑ z)
  where
    open Preorder pre

is-upper-bound : ∀ {A} → Preorder A → A → A → A → Set
is-upper-bound pre a b z = (a ⊑ z) × (b ⊑ z)
  where
    open Preorder pre

is-lower-bound : ∀ {A} → Preorder A → A → A → A → Set
is-lower-bound pre a b z = (z ⊑ a) × (z ⊑ b)
  where
    open Preorder pre

is-lub : ∀ {A} → Preorder A → A → A → A → Set
is-lub pre a b = is-least pre (is-upper-bound pre a b)

is-glb : ∀ {A} → Preorder A → A → A → A → Set
is-glb pre a b = is-greatest pre (is-lower-bound pre a b)

record PartialOrder (A : Set) : Set₁ where
  field
    preorder : Preorder A
  open Preorder preorder
  field
    antisym : ∀ {a b} → a ⊑ b → b ⊑ a → a ≡ b


record Lattice (A : Set) : Set₁ where
  field
    porder : PartialOrder A
  open PartialOrder porder
  field
    lub-exists : ∀ a b → ∃[ z ] is-lub preorder a b z
    glb-exists : ∀ a b → ∃[ z ] is-glb preorder a b z

  lub : A → A → A
  lub a b = proj₁ (lub-exists a b)

  glb : A → A → A
  glb a b = proj₁ (glb-exists a b)

  lub-is-lub : ∀ {a b} → is-lub preorder a b (lub a b)
  lub-is-lub {a} {b} = proj₂ (lub-exists a b)

  lub-is-upper-bound : ∀ {a b} → is-upper-bound preorder a b (lub a b)
  lub-is-upper-bound {a} {b} = proj₁ (lub-is-lub {a} {b})

  glb-is-glb : ∀ {a b} → is-glb preorder a b (glb a b)
  glb-is-glb {a} {b} = proj₂ (glb-exists a b)

  glb-is-lower-bound : ∀ {a b} → is-lower-bound preorder a b (glb a b)
  glb-is-lower-bound {a} {b} = proj₁ glb-is-glb

is-Upper-Bound : ∀ {I A} → Preorder A → (I → A) → A → Set
is-Upper-Bound pre X z =
  ∀ {i} → X i ⊑ z
  where
    open Preorder pre

is-Lub : ∀ {I A} → Preorder A → (I → A) → A → Set
is-Lub pre X z = is-least pre (is-Upper-Bound pre X) z

record DistributiveLattice (A : Set) : Set₁ where
  field
    lattice : Lattice A
  open Lattice lattice
  open PartialOrder porder
  field
    lub-distr-glb : ∀ {a b c} →
      lub a (glb b c) ≡ glb (lub a b) (lub a c)

    glb-distr-lub : ∀ {a b c} →
      glb a (lub b c) ≡ lub (glb a b) (glb a c)

is-top : ∀ {A} → Preorder A → A → Set
is-top preorder a = ∀ {z} → z ⊑ a
  where
    open Preorder preorder

is-bottom : ∀ {A} → Preorder A → A → Set
is-bottom preorder a = ∀ {z} → a ⊑ z
  where
    open Preorder preorder

is-bounded : ∀ {A} → Preorder A → Set
is-bounded preorder =
  (∃[ t ] is-top preorder t)
    ×
  (∃[ f ] is-bottom preorder f)

record Frame (A : Set) : Set₁ where
  field
    distr-lattice : DistributiveLattice A
  open DistributiveLattice distr-lattice
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder
  field
    Lub-exists : ∀ {I} (X : I → A) → ∃[ z ] is-Lub preorder X z

    ⊤ : A
    ⊤-is-top : is-top preorder ⊤

  Lub : ∀ {I} (X : I → A) → A
  Lub X = proj₁ (Lub-exists X)

  Lub-is-Lub : ∀ {I} {X : I → A} → is-Lub preorder X (Lub X)
  Lub-is-Lub {_} {X} = proj₂ (Lub-exists X)

  Lub-is-upper-bound : ∀ {I} {X : I → A} →
    ∀ {i} →
    X i ⊑ Lub X
  Lub-is-upper-bound {_} {X} {i} =
    let _ , q , _ = Lub-exists X
    in
    q

  field
    Lub-distr-glb : ∀ {I} {a} (B : I → A) →
      glb a (Lub B) ≡ Lub (λ i → glb a (B i))


-- record Frame-morphism {A B : Set} (F-A : Frame A) (F-B : Frame B) : Set₁ where
--   open Frame F-A renaming (Lub to A-Lub; distr-lattice to A-distr-lattice)
--   open DistributiveLattice A-distr-lattice renaming (lattice to A-lattice)
--   open Lattice A-lattice renaming (glb to A-glb)

--   open Frame F-B renaming (Lub to B-Lub; distr-lattice to B-distr-lattice)
--   open DistributiveLattice B-distr-lattice renaming (lattice to B-lattice)
--   open Lattice B-lattice renaming (glb to B-glb)
  
--   field
--     act : A → B
--     preserves-glb : ∀ {a b} →
--       act (A-glb a b) ≡ B-glb (act a) (act b)

--     preserves-Lub : ∀ {I} {X : I → A} →
--       act (A-Lub X) ≡ B-Lub (λ i → act (X i))

-- Locale-morphism : {A B : Set} → Frame A → Frame B → Set₁
-- Locale-morphism F-A F-B = Frame-morphism F-B F-A

-- _F⇒_ = Frame-morphism
-- _L⇒_ = Locale-morphism

-- _F∘_ : ∀ {A B C} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} →
--   F-B F⇒ F-C →
--   F-A F⇒ F-B →
--   F-A F⇒ F-C
-- _F∘_ f g =
--   record
--     { act = λ x → Frame-morphism.act f (Frame-morphism.act g x)
--     ; preserves-glb = λ {a} {b} → trans (cong (Frame-morphism.act f) (Frame-morphism.preserves-glb g)) (Frame-morphism.preserves-glb f)
--     ; preserves-Lub = λ {I} {X} → trans (cong (Frame-morphism.act f) (Frame-morphism.preserves-Lub g)) (Frame-morphism.preserves-Lub f)
--     }

-- _L∘_ : ∀ {A B C} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} →
--   F-B L⇒ F-C →
--   F-A L⇒ F-B →
--   F-A L⇒ F-C
-- _L∘_ f g = g F∘ f

-- id-F : ∀ {A} {F-A : Frame A} → F-A F⇒ F-A
-- id-F =
--   record
--     { act = λ z → z
--     ; preserves-glb = refl
--     ; preserves-Lub = refl
--     }

-- -- TODO: Figure out a nice way to deal with equalities of proofs here:
-- -- F∘-assoc : ∀ {A B C D} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} {F-D : Frame D} →
-- --   {f : F-C F⇒ F-D} →
-- --   {g : F-B F⇒ F-C} →
-- --   {h : F-A F⇒ F-B} →
-- --   ((f F∘ g) F∘ h) ≡ (f F∘ (g F∘ h))
-- -- F∘-assoc {f = f} {g = g} {h = h} = {!!}
