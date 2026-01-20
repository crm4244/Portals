

import Portals.CategoryTheory.SideSpace


open TopologicalSpace Sides

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


def subrealizer_open (R : ComponentRealizer U S p) (V : Opens X) : Opens X := by
  -- take the intersection U ∩ V, split it into components, use only components that touch p
  -- recombine the components like interior(closure(union))
  sorry

def subrealizer (R : ComponentRealizer U S p) (V : Opens X) :
    ComponentRealizer (R.subrealizer_open V) S p := by

  sorry

theorem subrealizer_subset_left (R : ComponentRealizer U S p) (V : Opens X) :
    (R.subrealizer_open V).1 ⊆ U := by
  sorry


theorem subrealizer_subset_right (R : ComponentRealizer U S p) (V : Opens X) :
    (R.subrealizer_open V).1 ⊆ V := by
  sorry


end subrealizer




end ComponentRealizer




class RealizingSurface (S : Set X) (f : X → Opens X) where
  realizer (p : X) : ComponentRealizer (f p) S p


namespace RealizingSurface
-- realizers form a basis


end RealizingSurface

end Portal
