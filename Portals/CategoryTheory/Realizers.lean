

import Portals.CategoryTheory.SideSpace


open TopologicalSpace Sides

variable {X : Type} [TopologicalSpace X]


namespace Portal




class ComponentRealizer (S : Set X) (p : X) where
  set : Set X
  isOpen_set : IsOpen set
  mem_point : p ∈ set
  touching_component_inv : ConnectedComponents (Subtype (restrict_surface S set)ᶜ) →
    restricted_sides_at S set p
  touching_component_inv_isInvLeft : Function.LeftInverse touching_component_inv
    (restricted_touching_component_at S set p)
  touching_component_inv_isInvRight : Function.RightInverse touching_component_inv
    (restricted_touching_component_at S set p)


namespace ComponentRealizer

variable {S : Set X} {p : X}


theorem restricted_touching_component_at_bijective (R : ComponentRealizer S p) :
    Function.Bijective (restricted_touching_component_at S R.set p) :=
  ({
    toFun := restricted_touching_component_at S R.set p
    invFun := R.touching_component_inv
    left_inv := R.touching_component_inv_isInvLeft
    right_inv := R.touching_component_inv_isInvRight
  } : Equiv _ _ ).bijective


def side_transfer (R : ComponentRealizer S p) {σ : Sides S} (hσ : σ.center ∈ R.set) :
    {a : Sides S // a.center = p} :=
  have hom := homeomorph_thing S ⟨R.set, R.isOpen_set⟩
  have τ_q := touching_component (restrict_surface S R.set)
  have τ_p_inv := R.touching_component_inv
  have ρ := τ_p_inv (τ_q (hom ⟨σ, hσ⟩))
  have h_comm := congr_fun (lift_comm S ⟨R.set, R.isOpen_set⟩) ρ
  ⟨_, ρ.2 ▸ Function.comp_apply ▸ Function.comp_apply ▸ h_comm⟩


end ComponentRealizer




class RealizingSurface (S : Set X) where
  realizer (p : X) : ComponentRealizer S p





end Portal
