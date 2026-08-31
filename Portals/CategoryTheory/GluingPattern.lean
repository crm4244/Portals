
import Portals.CategoryTheory.Realizers
import Mathlib.Algebra.Group.Subgroup.Lattice


universe u v



variable {X : Type u}


namespace Portal

open ComponentRealizer



class GluingPattern (S : Set X) (G : Type v) [Group G] where
  map {p : X} (a b : SidesAt S p) : G
  trans {p : X} (a b c : SidesAt S p) :
      map a b * map b c = map a c


instance (S : Set X) (G : Type v) [Group G] : CoeFun (GluingPattern S G)
  (fun _ ↦ {p : X} → (_ _ : SidesAt S p) → G) where coe γ := @γ.map




namespace GluingPattern

variable {S : Set X} {G : Type v} [Group G] (γ : GluingPattern S G)



def isTrivial_at (p : X) : Prop := ∀ (a b : SidesAt S p), γ a b = 1
def isTrivial_on (A : Set X) := ∀ {p : A}, γ.isTrivial_at p
def isTrivial : Prop := γ.isTrivial_on ⊤


theorem refl_id
  {p : X} (a : SidesAt S p) :
    γ a a = 1 := by
  have h := γ.trans a a a
  nth_rw 3 [← mul_one (γ a a)] at h
  exact mul_left_cancel h


theorem symm_inv_right
    {p : X} (a b : SidesAt S p) : γ a b * γ b a = 1 :=
  (γ.trans a b a).trans (refl_id γ a)


theorem symm_inv_left
        {p : X} (a b : SidesAt S p) : γ b a * γ a b = 1 :=
  (γ.trans b a b).trans (refl_id γ b)


theorem congr_map {p p' : X} (h : p = p')
  {a b : SidesAt S p} {a' b' : SidesAt S p'} (ha : a ≍ a') (hb : b ≍ b') :
    γ a b = γ a' b' := by
  cases h; cases ha; cases hb; rfl


open TopologicalSpace

variable [TopologicalSpace X]



def respects_realizer {U : Opens X} {p : X} (R : ComponentRealizer U S p) : Prop :=
  ∀ {q : X} (hq : q ∈ U) (a b : SidesAt S q),
    γ (R.sidesAtTransfer hq a) (R.sidesAtTransfer hq b) = γ a b


def isLocallyConsistent : Prop :=
  ∀ {p : X}, ∃ (U : Opens X) (R : ComponentRealizer U S p), γ.respects_realizer R


def closure_range : Subgroup G := Subgroup.closure
  {P | ∃ (p : X) (a b : SidesAt S p), γ a b = P}




end GluingPattern


end Portal
