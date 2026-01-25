import Portals.CategoryTheory.EtaleSpace
--import Portals.Legacy.Basic

import Mathlib.CategoryTheory.Opposites
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
--X commutativity of τ and π

-- the composition gluing pattern
-- transitivity
-- local consistency
-- etc

-- the equality gluing pattern
-- transitivity
-- local consistency
-- etc



open Topology TopologicalSpace CategoryTheory Opposite TopCat Limits Sheaf

universe u
variable {X : Type u} [TopologicalSpace X]

namespace Portal





def punctured_components (S U : Set X) : Type u := ConnectedComponents (Subtype (U \ S))

def punctured_component_of_subset (S : Set X) {U V : Set X} (h : V ⊆ U) :
    punctured_components S V → punctured_components S U :=
  Continuous.connectedComponentsMap
    (Continuous.subtype_mk continuous_subtype_val fun ⟨_, hV, hS⟩ ↦ ⟨h hV, hS⟩)


/- this is the one i want to use -/
def precosheaf (S : Set X) : Opens X ⥤ Type u := {
  obj := fun U ↦ punctured_components S U
  map := fun {V U} f ↦ punctured_component_of_subset S f.le
  map_id := by intro; ext ⟨_⟩; rfl
  map_comp := by intros; ext ⟨_⟩; rfl
}


variable {FC : (Type u)ᵒᵖ → (Type u)ᵒᵖ → Type*} {CC : (Type u)ᵒᵖ → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory (Type u)ᵒᵖ FC]

def presheaf (S : Set X) : (TopCat.of X).Presheaf (Type u)ᵒᵖ := (precosheaf S).op

--#check fun S : Set X ↦ EtaleSpace (presheaf S)



-- for now im just writing in the behavior i need.
-- later this will use the co-etale space construction.
def Sides (S : Set X) : Type u := EtaleSpace (presheaf S)
instance instTopologicalSpaceSides (S : Set X) : TopologicalSpace (Sides S) := sorry



namespace Sides

variable {S : Set X}




def restrict_surface (S U : Set X) : Set U := (↑) ⁻¹' S
def touching_component {S : Set X} : Sides S → ConnectedComponents (Subtype Sᶜ) := sorry



section center

def center : Sides S → X := sorry

--theorem center_isLocalHomeomorph : IsLocalHomeomorph (center (S := S)) := sorry
theorem center_continuous : Continuous (center (S := S)) := sorry

end center



section components

def restricted_punctured_components (S U : Set X) : Type u :=
  ConnectedComponents (Subtype (restrict_surface S U)ᶜ)

def restrict_punctured_subtype {S U : Set X} :
    Subtype (U \ S) → Subtype (restrict_surface S U)ᶜ :=
  fun p ↦ ⟨⟨p.1, p.2.1⟩, p.2.2⟩

def lift_restricted_punctured_subtype {S U : Set X} :
    Subtype (restrict_surface S U)ᶜ → Subtype (U \ S) :=
  fun p ↦ ⟨p.1.1, p.1.2, p.2⟩

def restrict_punctured_component {S U : Set X} :
    punctured_components S U → restricted_punctured_components S U :=
  fun C ↦ by
  apply Quotient.map (sa := connectedComponentSetoid _)
    (restrict_punctured_subtype (S := S) (U := U))
  · intro ⟨a, haU, haS⟩ ⟨b, hbU, hbS⟩ hab
    unfold restrict_punctured_subtype
    unfold HasEquiv.Equiv instHasEquivOfSetoid connectedComponentSetoid at ⊢ hab
    simp? at ⊢ hab

    sorry
  exact C

def lift_restricted_punctured_component {S U : Set X} :
    restricted_punctured_components S U → punctured_components S U :=
  fun C ↦ by
  apply Quotient.map (sa := connectedComponentSetoid _)
    (lift_restricted_punctured_subtype (S := S) (U := U))
  · intro ⟨⟨a, haU⟩, haS⟩ ⟨⟨b, hbU⟩, hbS⟩ hab
    unfold lift_restricted_punctured_subtype
    unfold HasEquiv.Equiv instHasEquivOfSetoid connectedComponentSetoid at ⊢ hab
    simp? at ⊢ hab

    sorry
  exact C


/-
def punctured_components_restriction_equiv (S U : Set X) :
    Equiv (punctured_components S U) (restricted_punctured_components S U) :=
  {
    toFun := restrict_punctured_component S U
    invFun := lift_restricted_punctured_component S U
    left_inv := by sorry
    right_inv := by sorry
  }
-/


end components



section at_point

def sides_at (S : Set X) (p : X) : Set (Sides S) := { σ : Sides S | σ.center = p }

def restricted_sides_at (S : Set X) {U : Set X} {p : X} (hp : p ∈ U) :
    Set (Sides (restrict_surface S U)) :=
  sides_at (restrict_surface S U) ⟨p, hp⟩

def restricted_touching_component_at (S : Set X) {U : Set X} {p : X} (hp : p ∈ U) :
    restricted_sides_at S hp → restricted_punctured_components S U :=
  (restricted_sides_at S hp).restrict (touching_component (S := restrict_surface S U))

--theorem center_fiber_discrete (S : Set X) (p : X) : DiscreteTopology (sides_at S p) := sorry

end at_point



section map
universe v
variable {Y : Type v} [TopologicalSpace Y] {f : X → Y}

def map (hf : IsOpenEmbedding f) : Sides S → Sides (f '' S) := sorry

theorem map_comm (hf : IsOpenEmbedding f) (σ : Sides S) : (map hf σ).center = f σ.center := sorry

theorem isOpenEmbedding_map (hf : IsOpenEmbedding f) : IsOpenEmbedding (map (S := S) hf) := sorry

-- we might be able to export this to the etale space file
open Classical in noncomputable def homeomorph_pullback_center (hf : IsOpenEmbedding f) :
    Homeomorph (Sides S) { x : Sides (f '' S) × X // x.1.center = f x.2 } := by
  have h : Set.univ ≃ₜ _ := (isOpenEmbedding_map (S := S) hf).homeomorphImage Set.univ
  rw [Set.image_univ] at h
  apply (Homeomorph.Set.univ (Sides S)).symm.trans
  apply h.trans
  exact {
    toFun := fun ⟨a, ha⟩ ↦ ⟨⟨a, (choose ha).center⟩,
      (map_comm hf _) ▸ congr_arg center (choose_spec ha).symm⟩
    invFun := fun ⟨⟨σ, p⟩, h⟩ ↦ by
      simp? at h
      use σ
      simp?
      -- i think this requires reasoning about sheaves
      sorry
    left_inv := sorry
    right_inv := sorry
    continuous_toFun := sorry
    continuous_invFun := sorry
  }

end map



section lift
variable {U : Opens X}

def lift : Sides (restrict_surface S U) → Sides S := sorry

theorem lift_eq_map_subtypeVal (S : Set X) (U : Opens X) :
  lift (S := S) = map (IsOpen.isOpenEmbedding_subtypeVal U.2) := sorry

theorem lift_comm {U : Opens X} (σ : Sides (restrict_surface S U)) :
    σ.lift.center = σ.center :=
  lift_eq_map_subtypeVal S U ▸ map_comm (IsOpen.isOpenEmbedding_subtypeVal U.2) σ

theorem isOpenEmbedding_lift : IsOpenEmbedding (lift (S := S) (U := U)) :=
  lift_eq_map_subtypeVal S U ▸ isOpenEmbedding_map (IsOpen.isOpenEmbedding_subtypeVal U.2)

end lift



noncomputable def homeomorph_pullback_center_restrict (S : Set X) (U : Opens X) :
    Homeomorph (Sides (restrict_surface S U)) (center (S := S) ⁻¹' U) :=
  have h : IsOpenEmbedding Subtype.val := IsOpen.isOpenEmbedding_subtypeVal U.2
  (Subtype.range_coe_subtype ▸ SetLike.setOf_mem_eq U) ▸ Homeomorph.trans
    (homeomorph_pullback_center (S := restrict_surface S U) h)
    (pullbackHomeoPreimage center center_continuous Subtype.val h.isEmbedding)


theorem center_mem_of_restricted {U : Opens X} (σ : Sides (restrict_surface S U)) :
    σ.lift.center ∈ U :=
  σ.lift_comm ▸ σ.center.2


noncomputable def restrict_of_mem {U : Opens X} {σ : Sides S} (hσ : σ.center ∈ U) :
    Sides (restrict_surface S U) :=
  (homeomorph_pullback_center_restrict S U).symm ⟨σ, hσ⟩


theorem lift_restrict {U : Opens X} {σ : Sides S} (hσ : σ.center ∈ U) :
    (restrict_of_mem hσ).lift = σ := by

  sorry

theorem restrict_lift {U : Opens X} (σ : Sides (restrict_surface S U)) :
    restrict_of_mem σ.center_mem_of_restricted = σ :=
  isOpenEmbedding_lift.injective (lift_restrict σ.center_mem_of_restricted)


theorem restrict_comm {U : Opens X} {σ : Sides S} (hσ : σ.center ∈ U) :
    (restrict_of_mem hσ).center = σ.center :=
  (lift_restrict hσ ▸ lift_comm (restrict_of_mem hσ)).symm


def subsurface_colift {T : Set X} : S ⊆ T → Sides T → Sides S := sorry

-- if we can relax the isOpenEmbedding condition on Sides.map then we can use map_comm to prove this
theorem subsurface_colift_comm {T : Set X} (h : S ⊆ T) (σ : Sides T) :
  σ.center = (subsurface_colift h σ).center := sorry




end Sides



end Portal




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
