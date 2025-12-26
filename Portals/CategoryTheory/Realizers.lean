

import Portals.CategoryTheory.SideSpace


open TopologicalSpace Sides

variable {X : Type} [TopologicalSpace X]


namespace Portal


-- set --> carrier

class ComponentRealizer (S : Set X) (p : X) where
  domain : Opens X
  point_mem : p ∈ domain
  touching_component_inv : ConnectedComponents (Subtype (restrict_surface S domain)ᶜ) →
    restricted_sides_at S point_mem
  touching_component_inv_isInvLeft : Function.LeftInverse touching_component_inv
    (restricted_touching_component_at S point_mem)
  touching_component_inv_isInvRight : Function.RightInverse touching_component_inv
    (restricted_touching_component_at S point_mem)




namespace ComponentRealizer

variable {S : Set X} {p : X}




def restricted_surface (R : ComponentRealizer S p) : Set R.domain :=
  restrict_surface S R.domain

def punctured_component (R : ComponentRealizer S p) : Type :=
  ConnectedComponents (Subtype R.restricted_surfaceᶜ)




def equiv (R : ComponentRealizer S p) :
  Equiv (restricted_sides_at S R.point_mem)
    (ConnectedComponents (Subtype R.restricted_surfaceᶜ)) :=
  {
    toFun := restricted_touching_component_at S R.point_mem
    invFun := R.touching_component_inv
    left_inv := R.touching_component_inv_isInvLeft
    right_inv := R.touching_component_inv_isInvRight
  }


theorem restricted_touching_component_at_bijective (R : ComponentRealizer S p) :
    Function.Bijective (restricted_touching_component_at S R.point_mem) :=
  R.equiv.bijective



def touching_component (R : ComponentRealizer S p) :
    Sides R.restricted_surface → R.punctured_component :=
  Sides.touching_component (restrict_surface S R.domain)


def restricted_side_transfer (R : ComponentRealizer S p) (σ : Sides (restrict_surface S R.domain)) :
    restricted_sides_at S R.point_mem :=
  R.touching_component_inv (R.touching_component σ)


noncomputable def side_transfer (R : ComponentRealizer S p)
    {σ : Sides S} (hσ : σ.center ∈ R.domain) : Sides S :=
  (R.restricted_side_transfer (Sides.restrict_of_mem hσ)).1.lift


theorem center_eq_point_of_side_transfer (R : ComponentRealizer S p)
    {σ : Sides S} (hσ : σ.center ∈ R.domain) : (R.side_transfer hσ).center = p :=
  let σ_at_p := R.restricted_side_transfer (Sides.restrict_of_mem hσ)
  (σ_at_p.2 ▸ σ_at_p.1.lift_comm : σ_at_p.1.lift.center = (⟨_, R.point_mem⟩ : R.domain))




end ComponentRealizer




class RealizingSurface (S : Set X) where
  realizer (p : X) : ComponentRealizer S p





end Portal
