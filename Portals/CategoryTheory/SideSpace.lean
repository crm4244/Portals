import Portals.CategoryTheory.EtaleSpace
import Portals.Legacy.Basic

import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Order.Filter.Germ.Basic



-- Here's an outline of the things i need to write


-- Define the components presheaf
-- define sidespace of a TopCat morphism as etalespace of the sheafifcation
-- sidesspace as a functor Top ↓ Top → Top
-- projection into components
-- commutativity of stuff

-- portal maps can be its own short file with just the definition. Maybe unneccesary

-- for another file:
-- component realizing function φ
-- component realizers as discrete fibrations
-- portal maps preserve component realizers
-- do component realizers form a subcategory / subfunctor?
-- component transport function τ = φₚ⁻¹ ∘ φₐq

-- for later:
-- gluing pattern on an arbitrary group
-- transitivity
-- local consistency
-- the other local condition about unique representation
-- groupoid form
-- Material space as the orbit space of the groupoid

-- the union surface
-- the recommendation maps
-- commutativity of τ and π. What was π again?

-- the composition gluing pattern
-- transitivity
-- local consistency
-- etc

-- the equality gluing pattern
-- transitivity
-- local consistency
-- etc



open Topology TopologicalSpace CategoryTheory Opposite TopCat Limits


#check connectedComponentIn_lemma_3
#check components
#check ConnectedComponents
#check Quot.map
#check Presheaf.germ







#check default
#check Inhabited
#check fun X [TopologicalSpace X] (A : Set (ConnectedComponents X)) ↦ ConnectedComponents.mk ⁻¹' A


/- this is the one i want to use -/
def precosheaf {X : TopCat} (S : Set X) : Opens X ⥤ Type :=
{
  obj := fun U ↦ ConnectedComponents (Subtype (U.1 \ Sᶜ))
  map := fun {V U} f ↦
    let t : Subtype (V.1 \ Sᶜ) → Subtype (U.1 \ Sᶜ) := fun v ↦ ⟨v.1, f.le v.2.1, v.2.2⟩
    Continuous.connectedComponentsMap
      (Continuous.subtype_mk continuous_subtype_val _ : Continuous t)
  map_id := by intro; ext ⟨_⟩; rfl
  map_comp := by intros; ext ⟨_⟩; rfl
}



noncomputable def precosheaf2 {X S : TopCat} (i : S ⟶ X) : Over X ⥤ Type := {
  obj := fun f ↦ ConnectedComponents ↑(pullback i f.hom)
  map := fun {g f} t ↦
    let t' := pullback.map i g.hom i f.hom (𝟙 _) t.left (𝟙 _) rfl (by cat_disch)
    Quot.map t' (fun a b hab ↦
      connectedComponent_eq ((hab ▸ Continuous.image_connectedComponent_subset
      (ConcreteCategory.hom t').continuous a) ⟨b, mem_connectedComponent, rfl⟩))
  map_id := by intro; ext ⟨_⟩; cat_disch
  map_comp := by
    intros
    ext ⟨_⟩
    simp only [Functor.id_obj, Over.comp_left, types_comp_apply, Quot.map]
    rw [← ConcreteCategory.comp_apply]
    rw [pullback.map_comp]
    rfl
}



/- a working version that doesnt account for S -/
def precosheaf3 {X S : TopCat} (i : S ⟶ X) : Over X ⥤ Type := {
  obj := fun U ↦ ConnectedComponents U.left
  map := fun {V U} f ↦ Quot.map f.left (fun a b hab ↦
    connectedComponent_eq ((hab ▸ Continuous.image_connectedComponent_subset
    (ConcreteCategory.hom f.left).continuous a) ⟨b, mem_connectedComponent, rfl⟩))
  map_id := by intro; ext ⟨_⟩; rfl
  map_comp := by intros; ext ⟨_⟩; rfl
}
