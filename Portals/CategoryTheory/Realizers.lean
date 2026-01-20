

import Portals.CategoryTheory.SideSpace


open Topology TopologicalSpace Sides

variable {X : Type} [TopologicalSpace X]


namespace Portal


-- set --> carrier

class ComponentRealizer (U : Opens X) (S : Set X) (hub : X) where
  hub_mem : hub ∈ U
  touching_component_inv : ConnectedComponents (Subtype (restrict_surface S U)ᶜ) →
    restricted_sides_at S hub_mem
  touching_component_inv_isInvLeft : Function.LeftInverse touching_component_inv
    (restricted_touching_component_at S hub_mem)
  touching_component_inv_isInvRight : Function.RightInverse touching_component_inv
    (restricted_touching_component_at S hub_mem)




namespace ComponentRealizer

variable {U : Opens X} {S : Set X} {p : X}




def restricted_surface (R : ComponentRealizer U S p) : Set U :=
  restrict_surface S U

def punctured_component (R : ComponentRealizer U S p) : Type :=
  ConnectedComponents (Subtype (restrict_surface S U)ᶜ)




def equiv (R : ComponentRealizer U S p) :
  Equiv (restricted_sides_at S R.hub_mem)
    (ConnectedComponents (Subtype R.restricted_surfaceᶜ)) :=
  {
    toFun := restricted_touching_component_at S R.hub_mem
    invFun := R.touching_component_inv
    left_inv := R.touching_component_inv_isInvLeft
    right_inv := R.touching_component_inv_isInvRight
  }


theorem restricted_touching_component_at_bijective (R : ComponentRealizer U S p) :
    Function.Bijective (restricted_touching_component_at S R.hub_mem) :=
  R.equiv.bijective



def touching_component (R : ComponentRealizer U S p) :
    Sides R.restricted_surface → R.punctured_component :=
  Sides.touching_component R.restricted_surface


def restricted_side_transfer (R : ComponentRealizer U S p) (σ : Sides R.restricted_surface) :
    restricted_sides_at S R.hub_mem :=
  R.touching_component_inv (R.touching_component σ)


noncomputable def side_transfer (R : ComponentRealizer U S p)
    {σ : Sides S} (hσ : σ.center ∈ U) : Sides S :=
  (R.restricted_side_transfer (Sides.restrict_of_mem hσ)).1.lift


theorem center_eq_hub_of_side_transfer (R : ComponentRealizer U S p)
    {σ : Sides S} (hσ : σ.center ∈ U) : (R.side_transfer hσ).center = p :=
  let σ_at_p := R.restricted_side_transfer (Sides.restrict_of_mem hσ)
  (σ_at_p.2 ▸ σ_at_p.1.lift_comm : σ_at_p.1.lift.center = (⟨_, R.hub_mem⟩ : U))




section subrealizer


def subrealizing_open (R : ComponentRealizer U S p) {V : Opens X} (hV : p ∈ V) : Opens X :=
  {
    carrier := Subtype.val '' interior (closure (Subtype.val ''
      ⋃ C ∈ Sides.touching_component (restrict_surface S (U ∩ V)) ''
        (center (S := restrict_surface S (U ∩ V)) ⁻¹'
          {⟨p, R.hub_mem, hV⟩}), { x | Quot.mk _ x = C }))
    is_open' := (IsOpenEmbedding.isOpen_iff_image_isOpen (IsOpen.isOpenEmbedding_subtypeVal
      (IsOpen.inter U.2 V.2))).mp isOpen_interior
  }


theorem subrealizer_subset_inter (R : ComponentRealizer U S p) {V : Opens X} (hV : p ∈ V) :
    (R.subrealizing_open hV).1 ⊆ U ∩ V := fun _ ⟨x, _, h⟩ ↦ h ▸ x.2


theorem subrealizer_subset (R : ComponentRealizer U S p) {V : Opens X} (hV : p ∈ V) :
    (R.subrealizing_open hV).1 ⊆ U :=
  fun _ h ↦ (R.subrealizer_subset_inter hV h).1


theorem subrealizer_subset' (R : ComponentRealizer U S p) {V : Opens X} (hV : p ∈ V) :
    (R.subrealizing_open hV).1 ⊆ V :=
  fun _ h ↦ (R.subrealizer_subset_inter hV h).2


def subrealizer (R : ComponentRealizer U S p) {V : Opens X} (hV : p ∈ V) :
    ComponentRealizer (R.subrealizing_open hV) S p :=
  {
    hub_mem := by
      unfold subrealizing_open
      simp?
      -- maybe by contradiction? if V gets too close to p then p is in the boundary and V isnt open
      by_contra h

      sorry
    touching_component_inv := by

      intro C
      unfold subrealizing_open at C
      simp at C


      -- find the Component C' of U that C came from.
      #check R.subrealizer_subset hV
      #check (⟨U ∩ V, IsOpen.inter U.2 V.2⟩ : Opens X)
      #check restrict_components S (R.subrealizer_subset hV)
      -- map C' to a side of p in U using touching_component_inv
      #check R.touching_component_inv
      -- restriction to a side of p in U ∩ V using restrict_of_mem with hV
      sorry

    touching_component_inv_isInvLeft := by sorry

    touching_component_inv_isInvRight := by sorry
  }



end subrealizer




end ComponentRealizer




class RealizingSurface (S : Set X) (f : X → Opens X) where
  realizer (p : X) : ComponentRealizer (f p) S p


namespace RealizingSurface
-- realizers form a basis


end RealizingSurface

end Portal
