{-# OPTIONS --prop #-}

open import FrameDefs
open import Data.Empty renaming (⊥ to Void; ⊥-elim to Void-elim)
open import Data.Unit renaming (⊤ to Unit; tt to unit) hiding (preorder)
open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (preorder; Extensionality)
open import Agda.Primitive

open import Order

module FrameProperties {A} (frame : Frame A) where
  open Frame frame
  open DistributiveLattice distr-lattice
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder
  open Implication frame

  open LatticeProps lattice
  -- open Tactics (porder)
  open DualLatticeProps lattice

  ⊥ : A
  ⊥ = Lub {Void} (λ x → Void-elim x) 

  ⊥-is-bottom : is-bottom preorder ⊥
  ⊥-is-bottom {z} = proj₂ Lub-is-Lub z λ {}

  Frame-bounded : is-bounded preorder
  Frame-bounded = (⊤ , ⊤-is-top) , (⊥ , ⊥-is-bottom)


  -- One direction of the universal property of _⇒_
  ⇒⊑ : ∀ {x a b} →
      glb x a ⊑ b →
      x ⊑ (a ⇒ b)
  ⇒⊑ {x} {a} {b} p = Lub-is-upper-bound {∃[ x ] (glb x a ⊑ b)} {λ i → proj₁ i} {x , p}

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

  module SmallFrames where
    open import Data.Unit renaming (⊤ to Unit; tt to mk-Unit) hiding (preorder)
    open import Data.Empty renaming (⊥ to Empty; ⊥-elim to Empty-elim)
    -- open import Axiom.Extensionality.Propositional
  
    -- postulate funext : Extensionality lzero lzero
  
    -- The inconsistent frame
    data 𝟙 : Set where
      𝟙-obj : 𝟙
  
    Ω : Set₁
    Ω = Prop
