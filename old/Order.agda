open import Data.Product
open import Relation.Binary.PropositionalEquality hiding (preorder)
open import Agda.Primitive
open import Level hiding (suc)

module Order
  where

module _ {ℓ} where
  record Preorder (A : Set ℓ) : Set (lsuc ℓ) where
    -- constructor mk-Preorder
    field
      _⊑_ : A → A → Set
      ⊑-refl : ∀ {x} → x ⊑ x
      ⊑-trans : ∀ {x y z} → x ⊑ y → y ⊑ z → x ⊑ z
  
  module _ {A : Set ℓ} where
    is-least : ∀ {m} → Preorder A → (A → Set m) → A → Set (ℓ ⊔ m)
    is-least pre P z =
      P z × (∀ w → P w → z ⊑ w)
      where
        open Preorder pre
    
    is-greatest : ∀ {m} → Preorder A → (A → Set m) → A → Set (ℓ ⊔ m)
    is-greatest pre P z =
      P z × (∀ w → P w → w ⊑ z)
      where
        open Preorder pre
    
    is-upper-bound : Preorder A → A → A → A → Set
    is-upper-bound pre a b z = (a ⊑ z) × (b ⊑ z)
      where
        open Preorder pre
    
    is-lower-bound : Preorder A → A → A → A → Set
    is-lower-bound pre a b z = (z ⊑ a) × (z ⊑ b)
      where
        open Preorder pre
    
    is-lub : Preorder A → A → A → A → Set ℓ
    is-lub pre a b = is-least pre (is-upper-bound pre a b)
    
    is-glb : Preorder A → A → A → A → Set ℓ
    is-glb pre a b = is-greatest pre (is-lower-bound pre a b)
    
    is-top : Preorder A → A → Set ℓ
    is-top preorder a = ∀ {z} → z ⊑ a
      where
        open Preorder preorder
    
    is-bottom : Preorder A → A → Set ℓ
    is-bottom preorder a = ∀ {z} → a ⊑ z
      where
        open Preorder preorder
    
    is-bounded : Preorder A → Set ℓ
    is-bounded preorder =
      (∃[ t ] is-top preorder t)
        ×
      (∃[ f ] is-bottom preorder f)
    
    
  record PartialOrder (A : Set ℓ) : Set (lsuc ℓ) where
    -- constructor mk-PartialOrder
    field
      preorder : Preorder A
    open Preorder preorder
    field
      antisym : ∀ {a b} → a ⊑ b → b ⊑ a → a ≡ b
  
  module Chains {A : Set ℓ} (preorder : Preorder A) where
    open import Data.Nat
  
    open Preorder preorder
  
    ω-set : Set ℓ
    ω-set = ℕ → A
  
    is-ω-chain : ω-set → Set
    is-ω-chain C = ∀ {i} →
      C i ⊑ C (suc i)
  
    is-ω-set-upper-bound : ω-set → A → Set
    is-ω-set-upper-bound C z = ∀ {i} → C i ⊑ z
  
    is-ω-set-lub : ω-set → A → Set ℓ
    is-ω-set-lub C = is-least preorder (is-ω-set-upper-bound C)
  
  module CPO where
    open import Data.Sum
  
    record ωCPO (A : Set ℓ) : Set (lsuc ℓ) where
      field
        porder : PartialOrder A
      open PartialOrder porder
      open Preorder preorder
      open Chains preorder
      field
        ω-lub-exists : ∀ {C} → is-ω-chain C → ∃[ z ] is-ω-set-lub C z
  
      ω-lub : ∀ {C} → is-ω-chain C → A
      ω-lub {C} C-chain = proj₁ (ω-lub-exists {C} C-chain)
  
      ω-lub-is-lub : ∀ {C} → (C-chain : is-ω-chain C) → is-ω-set-lub C (ω-lub {C} C-chain)
      ω-lub-is-lub {C} C-chain = proj₂ (ω-lub-exists {C} C-chain)
  
      ω-lub-is-upper-bound : ∀ {C} → (C-chain : is-ω-chain C) →
        ∀ i →
        C i ⊑ ω-lub {C} C-chain
      ω-lub-is-upper-bound {C} C-chain _ =
        let _ , q , _ = ω-lub-exists {C} C-chain
        in
        q
  
    record Pointed-ωCPO (A : Set ℓ) : Set (lsuc ℓ) where
        field
          cpo : ωCPO A
        open ωCPO cpo
        open PartialOrder porder
        open Chains preorder
        field
          ⊥ : A
          ⊥-is-bottom : is-bottom preorder ⊥
  
        -- ω-chain-stabilizes : ∀ C → is-ω-chain C → Set
        -- ω-chain-stabilizes C C-chain =
        --     (∀ {i} → C i ≡ ⊥) ⊎ (∃[ i ] C i ≢ ⊥)
  
    -- -- A pointed ωCPO where every ω-chain stabilizes
    -- record Pointed-SωCPO (A : Set) : Set₁ where
    --   field
    --     pcpo : Pointed-ωCPO A
  
  record Lattice (A : Set ℓ) : Set (lsuc ℓ) where
    -- constructor mk-Lattice
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
  
  is-Upper-Bound : ∀ {I} {A : Set ℓ} → Preorder A → (I → A) → A → Set
  is-Upper-Bound pre X z =
    ∀ {i} → X i ⊑ z
    where
      open Preorder pre
  
  is-Lub : ∀ {I} {A : Set ℓ} → Preorder A → (I → A) → A → Set ℓ
  is-Lub pre X z = is-least pre (is-Upper-Bound pre X) z
  
  record DistributiveLattice (A : Set ℓ) : Set (lsuc ℓ) where
    -- constructor mk-DistributiveLattice
    field
      lattice : Lattice A
    open Lattice lattice
    open PartialOrder porder
    field
      lub-distr-glb : ∀ {a b c} →
        lub a (glb b c) ≡ glb (lub a b) (lub a c)
  
      glb-distr-lub : ∀ {a b c} →
        glb a (lub b c) ≡ lub (glb a b) (glb a c)
  
  record Frame (A : Set ℓ) : Set (lsuc ℓ) where
    -- constructor mk-Frame
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

module Implication {A : Set} (frame : Frame A) where
  open Frame frame
  open DistributiveLattice distr-lattice
  open Lattice lattice
  open PartialOrder porder
  open Preorder preorder

  -- Heyting implication
  _⇒_ : A → A → A
  _⇒_ u v = Lub {∃[ x ] (glb x u ⊑ v)} λ i → proj₁ i

open Implication
