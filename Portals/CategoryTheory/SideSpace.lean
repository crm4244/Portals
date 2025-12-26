--import Portals.CategoryTheory.EtaleSpace
--import Portals.Legacy.Basic

import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
--import Mathlib.Order.Filter.Germ.Basic



-- Here's an outline of the things i need to write

--X Define the components presheaf
-- define sidespace of a TopCat morphism as etalespace of the sheafifcation
-- sidesspace as a functor Top ↓ Top → Top
-- projection into components
-- commutativity of stuff

--X portal maps can be its own short file with just the definition. Maybe unneccesary

-- for another file:
--X component realizing function φ
--X component realizers as discrete fibrations
-- portal maps preserve component realizers
-- do component realizers form a subcategory / subfunctor?
--X component transport function τ = φₚ⁻¹ ∘ φₐq

-- for later:
--X gluing pattern on an arbitrary group
--X transitivity
--X local consistency
-- the other local condition about unique representation
-- groupoid form
-- Material space as the orbit space of the groupoid

--X the union surface
--X the recommendation maps
-- commutativity of τ and π

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

variable {S : Set X}




def touching_component (S : Set X) : Sides S → ConnectedComponents (Subtype Sᶜ) := sorry



section center

def center : Sides S → X := sorry

--def center_isLocalHomeomorph : IsLocalHomeomorph (center (S := S)) := sorry
def center_continuous : Continuous (center (S := S)) := sorry
--def center_fiber_discrete (p : X) : DiscreteTopology {σ : Sides S // σ.center = p} := sorry

end center

def sides_at (S : Set X) (p : X) : Set (Sides S) := { σ : Sides S | σ.center = p }

def restrict_surface (S U : Set X) : Set U := (↑) ⁻¹' S

def restricted_sides_at (S : Set X) {U : Set X} {p : X} (hp : p ∈ U) :
    Set (Sides (restrict_surface S U)) :=
  sides_at (restrict_surface S U) ⟨p, hp⟩

def restricted_touching_component_at (S : Set X) {U : Set X} {p : X} (hp : p ∈ U) :
    restricted_sides_at S hp → ConnectedComponents (Subtype (restrict_surface S U)ᶜ) :=
  (restricted_sides_at S hp).restrict (touching_component (restrict_surface S U))


section map
variable {Y : Type} [TopologicalSpace Y] {f : X → Y}

def map (hf : IsOpenEmbedding f) : Sides S → Sides (f '' S) := sorry

theorem map_comm (hf : IsOpenEmbedding f) (σ : Sides S) : (map hf σ).center = f (σ.center) := sorry

theorem isOpenEmbedding_map (hf : IsOpenEmbedding f) : IsOpenEmbedding (map (S := S) hf) := sorry

def homeomorph_pullback_center (hf : IsOpenEmbedding f) :
    Homeomorph (Sides S) { p : Sides (f '' S) × X // center p.1 = f p.2 } := by
  have h : Set.univ ≃ₜ _ := (isOpenEmbedding_map (S := S) hf).homeomorphImage Set.univ
  simp? at h
  rw [Set.image_univ] at h
  #check Set.univ_subtype
  sorry

end map


section lift
variable {U : Opens X}

def lift : Sides (restrict_surface S U) → Sides S := sorry

theorem lift_eq_map_subtypeVal (S : Set X) (U : Opens X) : lift (S := S) =
  map (IsOpen.isOpenEmbedding_subtypeVal U.2) := sorry

theorem lift_comm {U : Opens X} (σ : Sides (restrict_surface S U)) :
    σ.lift.center = σ.center :=
  lift_eq_map_subtypeVal S U ▸ map_comm (IsOpen.isOpenEmbedding_subtypeVal U.2) σ

theorem isOpenEmbedding_lift : IsOpenEmbedding (lift (S := S) (U := U)) :=
  lift_eq_map_subtypeVal S U ▸ isOpenEmbedding_map (IsOpen.isOpenEmbedding_subtypeVal U.2)

end lift



noncomputable def homeomorph_pullback_center_restrict (S : Set X) (U : Opens X) :
    Homeomorph (Sides (restrict_surface S U)) (center (S := S) ⁻¹' U) :=
  have hemb : IsOpenEmbedding Subtype.val := IsOpen.isOpenEmbedding_subtypeVal U.2
  (Subtype.range_coe_subtype ▸ SetLike.setOf_mem_eq U) ▸ Homeomorph.trans
    (homeomorph_pullback_center (S := restrict_surface S U) hemb)
    (pullbackHomeoPreimage center center_continuous Subtype.val hemb.isEmbedding)


theorem center_mem_of_restricted {U : Opens X} (σ : Sides (restrict_surface S U)) :
    σ.lift.center ∈ U :=
  σ.lift_comm ▸ σ.center.2


noncomputable def restrict_of_mem {U : Opens X} {σ : Sides S} (hσ : σ.center ∈ U) :
    Sides (restrict_surface S U) :=
  (Sides.homeomorph_pullback_center_restrict S U).symm ⟨σ, hσ⟩


theorem center_eq_of_restrict {S : Set X} {U : Opens X} {a b : Sides S}
  (hab : a.center = b.center) (hmem : a.center ∈ U) :
    (Sides.restrict_of_mem hmem).center = (Sides.restrict_of_mem (hab ▸ hmem)).center := by
  -- we need something about how Subtype.val ⁻¹' is a homeomorphism

  simp?

  sorry


theorem lift_restrict {U : Opens X} {σ : Sides S} (hσ : σ.center ∈ U) :
    (restrict_of_mem hσ).lift = σ := by

  sorry

theorem restrict_lift {U : Opens X} (σ : Sides (restrict_surface S U)) :
    restrict_of_mem σ.center_mem_of_restricted = σ :=
  isOpenEmbedding_lift.injective (lift_restrict σ.center_mem_of_restricted)


def subsurface_colift {T : Set X} : S ⊆ T → Sides T → Sides S := sorry

-- if we can relax the isOpenEmbedding condition on Sides.map then we can use map_comm to prove this
theorem subsurface_colift_comm {T : Set X} (h : S ⊆ T) (σ : Sides T) :
  σ.center = (subsurface_colift h σ).center := sorry




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
