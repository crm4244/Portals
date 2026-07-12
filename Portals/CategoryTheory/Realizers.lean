

import Portals.CategoryTheory.SideSpace

open Topology TopologicalSpace

variable {X : Type} [TopologicalSpace X]







namespace Portal

open Sides




class ComponentRealizer (U : Opens X) (S : Set X) (hub : X) where
  hub_mem : hub ∈ U
  touching_component_inv : restricted_punctured_components S U →
    restricted_at S hub_mem
  touching_component_left_inv : Function.LeftInverse touching_component_inv
    (restricted_touching_component_at S hub_mem)
  touching_component_right_inv : Function.RightInverse touching_component_inv
    (restricted_touching_component_at S hub_mem)




namespace ComponentRealizer

variable {U : Opens X} {S : Set X} {p : X}


section Defs

set_option linter.unusedVariables false



def restricted_surface (R : ComponentRealizer U S p) : Set U :=
  restrict_surface S U


def punctured_components (R : ComponentRealizer U S p) : Type :=
  restricted_punctured_components S U



end Defs



def restricted_hub (R : ComponentRealizer U S p) : U := ⟨p, R.hub_mem⟩




def equiv (R : ComponentRealizer U S p) :
  Equiv (restricted_at S R.hub_mem) R.punctured_components := {
    toFun := restricted_touching_component_at S R.hub_mem
    invFun := R.touching_component_inv
    left_inv := R.touching_component_left_inv
    right_inv := R.touching_component_right_inv
  }


theorem restricted_touching_component_at_bijective (R : ComponentRealizer U S p) :
  Function.Bijective (restricted_touching_component_at S R.hub_mem) :=
   R.equiv.bijective



def touching_component (R : ComponentRealizer U S p) :
  Sides R.restricted_surface → R.punctured_components :=
   Sides.touching_component (S := R.restricted_surface)


def restricted_side_transfer (R : ComponentRealizer U S p) (σ : Sides R.restricted_surface) :
  restricted_at S R.hub_mem :=
   R.touching_component_inv (R.touching_component σ)


noncomputable def side_transfer (R : ComponentRealizer U S p)
  (σ : Sides S) (hσ : σ.center ∈ U := by aesop) : Sides S :=
    (R.restricted_side_transfer (σ.restrict_of_mem)).1.lift


theorem center_eq_hub_of_side_transfer (R : ComponentRealizer U S p)
  (σ : Sides S) (hσ : σ.center ∈ U := by aesop) :
    (R.side_transfer σ).center = p :=
  let σ_at_p := R.restricted_side_transfer σ.restrict_of_mem
  (σ_at_p.2 ▸ σ_at_p.1.lift_comm : σ_at_p.1.lift.center = (⟨_, R.hub_mem⟩ : U))


noncomputable def side_transfer_at (R : ComponentRealizer U S p)
  {q : X} (hq : q ∈ U) (σ : Sides.at_point S q) : Sides.at_point S p :=
    let hσ : σ.1.center ∈ U := σ.2.symm ▸ hq
    ⟨R.side_transfer σ.1 hσ, R.center_eq_hub_of_side_transfer σ.1 hσ⟩






end ComponentRealizer



end Portal
