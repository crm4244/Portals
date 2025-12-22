--import Portals.CategoryTheory.EtaleSpace
--import Portals.Legacy.Basic

import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
--import Mathlib.Order.Filter.Germ.Basic



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




variable {X : Type} [TopologicalSpace X]




/- this is the one i want to use -/
def precosheaf (S : Set X) : Opens X ⥤ Type := {
  obj := fun U ↦ ConnectedComponents (Subtype (U.1 \ S))
  map := fun {V U} f ↦ Continuous.connectedComponentsMap
    (Continuous.subtype_mk continuous_subtype_val fun ⟨_, hV, hS⟩ ↦ ⟨f.le hV, hS⟩)
  map_id := by intro; ext ⟨_⟩; rfl
  map_comp := by intros; ext ⟨_⟩; rfl
}





-- for now im just writing in the behavior i need.
-- later this will use the co-etale space construction.
def Sides (S : Set X) : Type := sorry
instance instTopologicalSpaceSideSpace (S : Set X) : TopologicalSpace (Sides S) := sorry


namespace Sides


def touching_component (S : Set X) : Sides S → ConnectedComponents (Subtype Sᶜ) := sorry


section center
variable {S : Set X}

def center : Sides S → X := sorry
def center' (S : Set X) := center (S := S)

def center_isLocalHomeomorph : IsLocalHomeomorph (center' S) := sorry
def center_continuous : Continuous (center' S) := sorry
def center_fiber_discrete (p : X) : DiscreteTopology {σ : Sides S // σ.center = p} := sorry

end center


def restrict_surface (S : Set X) (U : Set X) : Set U := Subtype.val ⁻¹' S
def restricted_sides_at (S U : Set X) (p : X) : Set (Sides (restrict_surface S U)) :=
  {σ : Sides (restrict_surface S U) | σ.center = p}
def restricted_touching_component_at (S U : Set X) (p : X) :
    restricted_sides_at S U p → ConnectedComponents (Subtype (restrict_surface S U)ᶜ) :=
  (restricted_sides_at S U p).restrict (touching_component (restrict_surface S U))


section map
variable {Y : Type} [TopologicalSpace Y] {f : X → Y}

def map (S : Set X) (hf : IsOpenEmbedding f) : Sides S → Sides (f '' S) := sorry

def map_comm (S : Set X) (hf : IsOpenEmbedding f) :
  center' (f '' S) ∘ map S hf = f ∘ center' S := sorry
def homeomorph_pullback_center (S : Set X) (hf : IsOpenEmbedding f) :
  Homeomorph (Sides S) (pullback (C := TopCat) (ofHom ⟨f, hf.continuous⟩)
  (ofHom ⟨center' (f '' S), center_isLocalHomeomorph.continuous⟩)) := sorry

end map


section lift
variable {S : Set X} {U : Opens X}

def lift : Sides (restrict_surface S U) → Sides S := sorry
def lift' (S : Set X) (U : Opens X) := lift (S := S) (U := U)

lemma lift_eq_map_subtypeVal (S : Set X) (U : Opens X) : lift' S U =
  map (restrict_surface S U) (IsOpen.isOpenEmbedding_subtypeVal U.2) := sorry

def lift_comm (S : Set X) (U : Opens X) :
    center' S ∘ lift' S U = Subtype.val ∘ center' (restrict_surface S U) :=
  lift_eq_map_subtypeVal S U ▸ map_comm _ _

end lift


def homeomorph_pullback_center_restrict (S : Set X) (U : Opens X) :
  Homeomorph (center' S ⁻¹' U) (Sides (restrict_surface S U)) := sorry


def other_lift {S T : Set X} : S ⊆ T → Sides T → Sides S := sorry
def other_lift_comm {S T : Set X} (h : S ⊆ T) : center' T = center' S ∘ other_lift h := sorry


end Sides








/-

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
def precosheaf3 {X : TopCat} : Over X ⥤ Type := {
  obj := fun U ↦ ConnectedComponents U.left
  map := fun {V U} f ↦ Quot.map f.left (fun a b hab ↦
    connectedComponent_eq ((hab ▸ Continuous.image_connectedComponent_subset
    (ConcreteCategory.hom f.left).continuous a) ⟨b, mem_connectedComponent, rfl⟩))
  map_id := by intro; ext ⟨_⟩; rfl
  map_comp := by intros; ext ⟨_⟩; rfl
}


-/
