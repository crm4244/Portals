

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


noncomputable def side_transfer (R : ComponentRealizer S p) {σ : Sides S} (hσ : σ.center ∈ R.set) :
    {a : Sides S // a.center = p} :=
  let U : Opens X := ⟨_, R.isOpen_set⟩
  have hom := homeomorph_pullback_center_restrict S U
  have τ_q := touching_component (restrict_surface S R.set)
  have τ_p_inv := R.touching_component_inv
  have a := τ_p_inv (τ_q (hom.symm ⟨σ, hσ⟩))
  ⟨a.1.lift, a.2 ▸ lift_comm U a.1⟩



end ComponentRealizer




class RealizingSurface (S : Set X) where
  realizer (p : X) : ComponentRealizer S p





end Portal
