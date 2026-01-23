


import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks

open CategoryTheory Opposite Presheaf Topology TopologicalSpace

universe u v

variable (C : Type u) [Category.{v} C]
variable {X : TopCat}


#check op X
def TotalSpace (F : X.Presheaf (Type u)) := Σ x : X, stalk F x
def proj {F : X.Presheaf (Type u)} : Total F → X := Sigma.fst
