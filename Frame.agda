open import Data.Product
open import Agda.Primitive hiding (_⊔_)
open import Relation.Binary.PropositionalEquality hiding (preorder)

module Frame
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
      act (A-glb a b) ≡ B-glb (act a) (act b)

    preserves-Lub : ∀ {I} {X : I → A} →
      act (A-Lub X) ≡ B-Lub (λ i → act (X i))

Locale-morphism : {A B : Set} → Frame A → Frame B → Set₁
Locale-morphism F-A F-B = Frame-morphism F-B F-A

_F⇒_ = Frame-morphism
_L⇒_ = Locale-morphism

_F∘_ : ∀ {A B C} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} →
  F-B F⇒ F-C →
  F-A F⇒ F-B →
  F-A F⇒ F-C
_F∘_ f g =
  record
    { act = λ x → Frame-morphism.act f (Frame-morphism.act g x)
    ; preserves-glb = λ {a} {b} → trans (cong (Frame-morphism.act f) (Frame-morphism.preserves-glb g)) (Frame-morphism.preserves-glb f)
    ; preserves-Lub = λ {I} {X} → trans (cong (Frame-morphism.act f) (Frame-morphism.preserves-Lub g)) (Frame-morphism.preserves-Lub f)
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
    ; preserves-glb = refl
    ; preserves-Lub = refl
    }

-- TODO: Figure out a nice way to deal with equalities of proofs here:
-- F∘-assoc : ∀ {A B C D} {F-A : Frame A} {F-B : Frame B} {F-C : Frame C} {F-D : Frame D} →
--   {f : F-C F⇒ F-D} →
--   {g : F-B F⇒ F-C} →
--   {h : F-A F⇒ F-B} →
--   ((f F∘ g) F∘ h) ≡ (f F∘ (g F∘ h))
-- F∘-assoc {f = f} {g = g} {h = h} = {!!}

module LatticeProps {A} (lattice : Lattice A) where

  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder

  _⊔_ = lub
  _⊓_ = glb

  module Tactics where
    eq-⊑ : ∀ {a b} →
        a ≡ b →
        a ⊑ b
    eq-⊑ refl = ⊑-refl

    infixr 2 _⊢_⨾⟨_⟩_
    infix  3 _⊢_∎T
    infix  1 begin-tactics_

    _⊢_⨾⟨_⟩_ : ∀ {a b} {c d} e r →
        (c ⊑ d → e ⊑ r) →
        (a ⊑ b → c ⊑ d) →
        (a ⊑ b → e ⊑ r)
    _⊢_⨾⟨_⟩_ e r f g x = f (g x)

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


module DualLatticeProps {A} (lattice : Lattice A) where
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


module Locales {A} (frame : Frame A) where

  open Frame frame
  open DistributiveLattice distr-lattice
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder

  open LatticeProps lattice
  open Tactics
  open DualLatticeProps lattice

  open import Data.Empty renaming (⊥ to Void; ⊥-elim to Void-elim)
  open import Data.Unit renaming (⊤ to Unit; tt to unit) hiding (preorder)
  open import Data.Bool

  ⊥ : A
  ⊥ = Lub {Void} (λ x → Void-elim x) 

  ⊥-is-bottom : is-bottom preorder ⊥
  ⊥-is-bottom {z} = proj₂ Lub-is-Lub z λ {}

  Frame-bounded : is-bounded preorder
  Frame-bounded = (⊤ , ⊤-is-top) , (⊥ , ⊥-is-bottom)

  -- Heyting implication
  _⇒_ : A → A → A
  _⇒_ u v = Lub {∃[ x ] (glb x u ⊑ v)} λ i → proj₁ i

  -- One direction of the universal property of _⇒_
  ⇒⊑ : ∀ {x a b} →
    glb x a ⊑ b →
    x ⊑ (a ⇒ b)
  ⇒⊑ {x} {a} {b} p = Lub-is-upper-bound {∃[ x ] (glb x a ⊑ b)} {λ i → proj₁ i} {x , p}

  app-1 : ∀ {a b} →
    glb a (a ⇒ b) ⊑ b
  app-1 {a} {b} rewrite Lub-distr-glb {∃[ x ] (glb x a ⊑ b)} {a} (λ i → proj₁ i) =
    proj₂ Lub-is-Lub b λ {i} → let j , k = i in ⊑-trans (eq-⊑ (glb-comm {a} {j})) k

  app-1′ : ∀ {a b} →
    glb (a ⇒ b) a ⊑ b
  app-1′ = ⊑-trans (eq-⊑ glb-comm) app-1

  -- The other direction of the universal property of _⇒_
  ⊑⇒ : ∀ {x a b} →
    x ⊑ (a ⇒ b) →
    glb x a ⊑ b
  ⊑⇒ {x} {a} {b} p =
    ⊑-trans (glb-monotone p ⊑-refl) (⊑-trans (eq-⊑ glb-comm) app-1)

  pair : ∀ (a b : A) → Bool → A
  pair a b false = a
  pair a b true = b

  Lub-lub : ∀ {a b} →
    lub a b ≡ Lub {Bool} (pair a b)
  Lub-lub {a} {b} =
    antisym
      (proj₂ lub-is-lub (Lub (pair a b)) (Lub-is-upper-bound , Lub-is-upper-bound))
      (proj₂ Lub-is-Lub (lub a b) (λ { {false} → proj₁ lub-is-upper-bound; {true} → proj₂ lub-is-upper-bound }))

  a⇒a : ∀ {a} →
    (a ⇒ a) ≡ ⊤
  a⇒a {a} =
    antisym
      ⊤-is-top
      (Lub-is-upper-bound {∃[ x ] glb x a ⊑ a} {λ i → let j , k = i in j} {⊤ , proj₂ glb-is-lower-bound})

  app≡ : ∀ {a b} →
    glb a (a ⇒ b) ≡ glb a b
  app≡ {a} {b} =
    antisym
      (proj₂ glb-is-glb (glb a (a ⇒ b)) (p1 , p4))
      (glb-monotone ⊑-refl (Lub-is-upper-bound {∃[ x ] glb x a ⊑ b} {λ i → proj₁ i} {b , proj₁ glb-is-lower-bound}))
    where
      p1  : glb a (a ⇒ b) ⊑ a
      p1 = proj₁ glb-is-lower-bound

      p2 : glb a (a ⇒ b) ⊑ (a ⇒ b)
      p2 = proj₂ glb-is-lower-bound

      p3 : glb (glb a (a ⇒ b)) a ⊑ b
      p3 = ⊑⇒ p2

      p4 : glb a (a ⇒ b) ⊑ b
      p4 = ⊑-trans (⊑-trans (eq-⊑ glb-comm) (⊑-trans (eq-⊑ glb-comm) (eq-⊑ (sym glb-a-b-a)))) p3

  app-2 : ∀ {a b} →
    glb b (a ⇒ b) ≡ b
  app-2 {a} {b} =
    antisym
      (proj₁ glb-is-lower-bound)
      (proj₂ glb-is-glb b (⊑-refl , ⇒⊑ (proj₁ glb-is-lower-bound)))

  ⇒const : ∀ {a b} →
    b ⊑ (a ⇒ b)
  ⇒const = ⇒⊑ (proj₁ glb-is-lower-bound)

  ⇒const-glb : ∀ {a b} →
    b ⊑ (a ⇒ glb a b)
  ⇒const-glb = ⇒⊑ (eq-⊑ glb-comm)

  ⇒-distr : ∀ {a b c} →
    a ⇒ (glb b c) ≡ glb (a ⇒ b) (a ⇒ c)
  ⇒-distr {a} {b} {c} =
    antisym
      q
      (⇒⊑ q2)
    where
      p1 : (a ⇒ glb b c) ⊑ (a ⇒ b)
      p1 = Lub-is-upper-bound {∃[ x ] glb x a ⊑ b} {λ x → proj₁ x} {Lub (λ x → proj₁ x) , ⊑-trans app-1′ (proj₁ glb-is-lower-bound)}

      p2 : (a ⇒ glb b c) ⊑ (a ⇒ c)
      p2 = Lub-is-upper-bound {∃[ x ] glb x a ⊑ c} {λ x → proj₁ x} {Lub (λ x → proj₁ x) , ⊑-trans app-1′ (proj₂ glb-is-lower-bound)}

      q : (a ⇒ glb b c) ⊑ glb (a ⇒ b) (a ⇒ c)
      q = (proj₂ glb-is-glb (Lub proj₁) (p1 , p2))

      lb1 : glb (glb a c) (glb a b) ⊑ b
      lb1 =
        begin
          glb (glb a c) (glb a b) ⊑⟨ glb-monotone ⊑-refl (proj₂ glb-is-lower-bound) ⟩
          glb (glb a c) b         ⊑⟨ proj₂ glb-is-lower-bound ⟩
          b
        ∎

      lb2 : glb (glb a c) (glb a b) ⊑ c
      lb2 =
        begin
          glb (glb a c) (glb a b) ⊑⟨ glb-monotone (proj₂ glb-is-lower-bound) ⊑-refl ⟩
          glb c (glb a b)         ⊑⟨ proj₁ glb-is-lower-bound ⟩
          c
        ∎

      q2 : glb (glb (a ⇒ b) (a ⇒ c)) a ⊑ glb b c
      q2 =
        begin
          glb (glb (a ⇒ b) (a ⇒ c)) a         ⊑⟨ glb-monotone ⊑-refl (eq-⊑ (sym glb-idem)) ⟩
          glb (glb (a ⇒ b) (a ⇒ c)) (glb a a) ⊑⟨ eq-⊑ glb-comm ⟩
          glb (glb a a) (glb (a ⇒ b) (a ⇒ c)) ⊑⟨ eq-⊑ (sym glb-assoc) ⟩
          glb a (glb a (glb (a ⇒ b) (a ⇒ c))) ⊑⟨ glb-monotone ⊑-refl (eq-⊑ glb-assoc) ⟩
          glb a (glb (glb a (a ⇒ b)) (a ⇒ c)) ⊑⟨ glb-monotone ⊑-refl (glb-monotone (eq-⊑ app≡) ⊑-refl) ⟩
          glb a (glb (glb a b) (a ⇒ c))       ⊑⟨ glb-monotone ⊑-refl (eq-⊑ glb-comm) ⟩
          glb a (glb (a ⇒ c) (glb a b))       ⊑⟨ eq-⊑ glb-assoc ⟩
          glb (glb a (a ⇒ c)) (glb a b)       ⊑⟨ glb-monotone (eq-⊑ app≡) ⊑-refl ⟩
          glb (glb a c) (glb a b)             ⊑⟨ proj₂ glb-is-glb (glb (glb a c) (glb a b)) (lb1 , lb2) ⟩
          glb b c
        ∎

  ¬_ : A → A
  ¬_ x = x ⇒ ⊥

  -- _⇒_ is monotone in its second parameter
  ⇒-monotone : ∀ {a b b′} →
    b ⊑ b′ →
    (a ⇒ b) ⊑ (a ⇒ b′)
  ⇒-monotone {a} {b} {b′} p =
    ⇒⊑ (⊑-trans app-1′ p)

  -- _⇒_ is antitone in its first parameter
  ⇒-antitone : ∀ {a a′ b} →
    a′ ⊑ a →
    (a ⇒ b) ⊑ (a′ ⇒ b)
  ⇒-antitone {a} {a′} {b} p =
    ⇒⊑ (⊑-trans (glb-monotone ⊑-refl p) app-1′)

  glb-⊤ : ∀ {a} →
    glb a ⊤ ≡ a
  glb-⊤ {a} = antisym (proj₁ glb-is-lower-bound) (proj₂ glb-is-glb a (⊑-refl , ⊤-is-top))

  module FrameTactics where
    -- z, (a ⇒ b) ⊢ b   --->   z ⊢ a
    apply : ∀ {a b z} →
        z ⊑ a →
        glb z (a ⇒ b) ⊑ b
    apply p = ⊑-trans (glb-monotone p ⊑-refl) app-1

    -- a ⊢ b   --->   ⊢ a ⇒ b
    intro : ∀ {a b} →
        a ⊑ b →
        ⊤ ⊑ (a ⇒ b)
    intro p = ⇒⊑ (⊑-trans (proj₂ glb-is-lower-bound) p)

    -- a, b ⊢ c   --->   a ⊢ b ⇒ c
    intro-glb : ∀ {a b c} →
        glb a b ⊑ c →
        a ⊑ (b ⇒ c)
    intro-glb = ⇒⊑

    -- ⊢ a ⇒ b   --->   a ⊢ b
    generalize : ∀ {a b} →
        ⊤ ⊑ (a ⇒ b) →
        a ⊑ b
    generalize p = ⊑-trans (eq-⊑ (sym (glb-⊤))) (⊑-trans (eq-⊑ glb-comm) (⊑⇒ p))

  open FrameTactics


  glb-⊥ : ∀ {a} →
    glb a ⊥ ≡ ⊥
  glb-⊥ {a} =
    antisym
      (proj₂ glb-is-lower-bound)
      ⊥-is-bottom

  noncontradict : ∀ {a} →
    glb a (¬ a) ≡ ⊥
  noncontradict =
    antisym
      (⊑-trans (eq-⊑ app≡) (proj₂ glb-is-lower-bound))
      ⊥-is-bottom

  noncontradict′ : ∀ {a} →
    glb (¬ a) a ≡ ⊥
  noncontradict′ = trans glb-comm noncontradict

  contrapositive : ∀ {a b} →
    a ⊑ b →
    (¬ b) ⊑ (¬ a)
  contrapositive {a} {b} p =
    begin
      (¬ b)   ⊑⟨⟩
      (b ⇒ ⊥) ⊑⟨ ⇒-antitone p ⟩
      (¬ a)
    ∎

  contrapositive⇒ : ∀ {a b} →
    (a ⇒ b) ⊑ ((¬ b) ⇒ (¬ a))
  contrapositive⇒ {a} {b} =
    ⇒⊑ (⇒⊑ (
      begin
        glb (glb (a ⇒ b) (¬ b)) a ⊑⟨ eq-⊑ glb-comm ⟩
        glb a (glb (a ⇒ b) (¬ b)) ⊑⟨ eq-⊑ glb-assoc ⟩
        glb (glb a (a ⇒ b)) (¬ b) ⊑⟨ glb-monotone app-1 ⊑-refl ⟩
        glb b (¬ b) ⊑⟨ eq-⊑ noncontradict ⟩
        ⊥
      ∎
      ))

  ¬distr : ∀ {a b} →
    ¬ (lub a b) ≡ glb (¬ a) (¬ b)
  ¬distr {a} {b} =
    antisym p q
    where
      p : (¬ lub a b) ⊑ glb (¬ a) (¬ b)
      p =
        begin
          (¬ lub a b)                     ⊑⟨⟩
          (lub a b ⇒ ⊥)                   ⊑⟨ ⇒-monotone (eq-⊑ (sym (glb-⊥ {⊥}))) ⟩
          (lub a b ⇒ glb ⊥ ⊥)             ⊑⟨ eq-⊑ ⇒-distr ⟩
          glb (lub a b ⇒ ⊥) (lub a b ⇒ ⊥) ⊑⟨ glb-monotone (⇒-antitone (proj₁ lub-is-upper-bound)) (⇒-antitone (proj₂ lub-is-upper-bound)) ⟩
          glb (a ⇒ ⊥) (b ⇒ ⊥)             ⊑⟨⟩
          glb (¬ a) (¬ b)
        ∎

      q₁ : ∀ {x y z} → x ⊑ z → y ⊑ z → lub x y ⊑ z
      q₁ {x} {y} {z} r s = proj₂ lub-is-lub z (r , s)

      q : glb (¬ a) (¬ b) ⊑ (¬ lub a b)
      q = ⇒⊑ (
        begin
          glb (glb (¬ a) (¬ b)) (lub a b)                         ⊑⟨ eq-⊑ glb-distr-lub ⟩
          lub (glb (glb (¬ a) (¬ b)) a) (glb (glb (¬ a) (¬ b)) b) ⊑⟨ lub-monotone (glb-monotone (eq-⊑ glb-comm) ⊑-refl) ⊑-refl ⟩
          lub (glb (glb (¬ b) (¬ a)) a) (glb (glb (¬ a) (¬ b)) b) ⊑⟨ lub-monotone (eq-⊑ (sym glb-assoc)) ⊑-refl ⟩
          lub (glb (¬ b) (glb (¬ a) a)) (glb (glb (¬ a) (¬ b)) b) ⊑⟨ lub-monotone (glb-monotone ⊑-refl (eq-⊑ noncontradict′)) ⊑-refl ⟩
          lub (glb (¬ b) ⊥) (glb (glb (¬ a) (¬ b)) b)             ⊑⟨ lub-monotone (proj₂ glb-is-lower-bound) ⊑-refl ⟩
          lub ⊥ (glb (glb (¬ a) (¬ b)) b)                         ⊑⟨ lub-monotone ⊑-refl (eq-⊑ (sym glb-assoc)) ⟩
          lub ⊥ (glb (¬ a) (glb (¬ b) b))                         ⊑⟨ lub-monotone ⊑-refl (glb-monotone ⊑-refl (eq-⊑ noncontradict′)) ⟩
          lub ⊥ (glb (¬ a) ⊥)                                     ⊑⟨ lub-monotone ⊑-refl (proj₂ glb-is-lower-bound) ⟩
          lub ⊥ ⊥                                                 ⊑⟨ eq-⊑ lub-idem ⟩
          ⊥
        ∎)

  ¬⊥ : (¬ ⊥) ≡ ⊤
  ¬⊥ = antisym ⊤-is-top (⇒⊑ (proj₂ glb-is-lower-bound))

  ¬¬intro : ∀ {a} →
    a ⊑ (¬ ¬ a)
  ¬¬intro {a} = Lub-is-upper-bound {∃[ x ] glb x (¬ a) ⊑ ⊥} {proj₁} {a , eq-⊑ noncontradict}

  ¬¬¬ : ∀ {a} →
    ¬ ¬ ¬ a ≡ ¬ a
  ¬¬¬ {a} =
      antisym p ¬¬intro
    where
      p : (¬ ¬ ¬ a) ⊑ (¬ a)
      p = ⇒⊑ (
        begin
          glb (¬ ¬ ¬ a) a           ⊑⟨⟩
          glb ((¬ ¬ a) ⇒ ⊥) a       ⊑⟨ glb-monotone ⊑-refl ¬¬intro ⟩
          glb ((¬ ¬ a) ⇒ ⊥) (¬ ¬ a) ⊑⟨ app-1′ ⟩
          ⊥
        ∎
        )

  ⊤⇒ : ∀ {a} →
    ⊤ ⇒ a ≡ a
  ⊤⇒ {a} = antisym p q
    where
      p : (⊤ ⇒ a) ⊑ a
      p =
        begin
          (⊤ ⇒ a)       ⊑⟨ eq-⊑ (sym (glb-⊤ {⊤ ⇒ a})) ⟩
          glb (⊤ ⇒ a) ⊤ ⊑⟨ app-1′ ⟩
          a
        ∎

      q : a ⊑ (⊤ ⇒ a)
      q =
        begin
          a ⊑⟨ ⇒⊑ (proj₁ glb-is-lower-bound) ⟩
          (⊤ ⇒ a)
        ∎

  ¬¬glb : ∀ {a b} →
    (¬ ¬ (glb a b)) ≡ glb (¬ ¬ a) (¬ ¬ b)
  ¬¬glb {a} {b} = antisym p q
    where
      p₁ : ∀ {x y z} →
        (z ⊑ x) →
        (z ⊑ y) →
        z ⊑ glb x y
      p₁ {x} {y} {z} r s = proj₂ glb-is-glb z (r , s)

      p₂ : (¬ ¬ (glb a b)) ⊑ (¬ ¬ a)
      p₂ =
        begin
          (¬ ¬ (glb a b))     ⊑⟨⟩
          ((glb a b ⇒ ⊥) ⇒ ⊥) ⊑⟨ ⇒-antitone (⇒-antitone (proj₁ glb-is-lower-bound)) ⟩
          (¬ ¬ a)
        ∎

      p₃ : (¬ ¬ (glb a b)) ⊑ (¬ ¬ b)
      p₃ =
        begin
          (¬ ¬ (glb a b))     ⊑⟨⟩
          ((glb a b ⇒ ⊥) ⇒ ⊥) ⊑⟨ ⇒-antitone (⇒-antitone (proj₂ glb-is-lower-bound)) ⟩
          (¬ ¬ b)
        ∎

      p : (¬ ¬ (glb a b)) ⊑ glb (¬ ¬ a) (¬ ¬ b)
      p = p₁ p₂ p₃

      q : glb (¬ ¬ a) (¬ ¬ b) ⊑ (¬ ¬ (glb a b))
      q =
        begin-tactics
            glb (¬ ¬ a) (¬ ¬ b)                   ⊢ ¬ ¬ glb a b  ⨾⟨ intro-glb ⟩
            glb (glb (¬ ¬ a) (¬ ¬ b)) (¬ glb a b) ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ (sym glb-assoc)) ⟩
            glb (¬ ¬ a) (glb (¬ ¬ b) (¬ glb a b)) ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ glb-comm) ⟩
            glb (glb (¬ ¬ b) (¬ glb a b)) (¬ ¬ a) ⊢ ⊥            ⨾⟨ apply ⟩
            glb (¬ ¬ b) (¬ glb a b)               ⊢ ¬ a          ⨾⟨ intro-glb ⟩
            glb (glb (¬ ¬ b) (¬ glb a b)) a       ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ (sym glb-assoc)) ⟩
            glb (¬ ¬ b) (glb (¬ glb a b) a)       ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ glb-comm) ⟩
            glb (glb (¬ glb a b) a) (¬ ¬ b)       ⊢ ⊥            ⨾⟨ apply ⟩
            glb (¬ glb a b) a                     ⊢ ¬ b          ⨾⟨ intro-glb ⟩
            glb (glb (¬ glb a b) a) b             ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ (sym glb-assoc)) ⟩
            glb (¬ glb a b) (glb a b)             ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ glb-comm) ⟩
            glb (glb a b) (¬ glb a b)             ⊢ ⊥            ⨾⟨ rewrite⊢ (eq-⊑ noncontradict) ⟩
            ⊥                                     ⊢ ⊥
        ∎T
