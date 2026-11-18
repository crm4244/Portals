
import PortalTheory.ComponentRealizer
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


@[simp] theorem refl_id
  {p : X} (a : SidesAt S p) :
    γ a a = 1 := by
  have h := γ.trans a a a
  nth_rw 3 [← mul_one (γ a a)] at h
  exact mul_left_cancel h


@[simp] theorem symm_inv_right
    {p : X} (a b : SidesAt S p) : γ a b * γ b a = 1 :=
  (γ.trans a b a).trans (refl_id γ a)


@[simp] theorem symm_inv_left
        {p : X} (a b : SidesAt S p) : γ b a * γ a b = 1 :=
  (γ.trans b a b).trans (refl_id γ b)


theorem congr_map {p p' : X} (h : p = p')
  {a b : SidesAt S p} {a' b' : SidesAt S p'} (ha : a.1 = a'.1) (hb : b.1 = b'.1) :
    γ a b = γ a' b' := by
  cases h
  cases Subtype.heq_iff_coe_eq (fun _ ↦ Iff.rfl) |>.mpr ha
  cases Subtype.heq_iff_coe_eq (fun _ ↦ Iff.rfl) |>.mpr hb
  rfl


open TopologicalSpace

variable [TopologicalSpace X]



def respects_realizer {U : Opens X} {p : X} (R : ComponentRealizer U S p) : Prop :=
  ∀ {q : X} (hq : q ∈ U) (a b : SidesAt S q),
    γ (R.sidesAtTransfer hq a) (R.sidesAtTransfer hq b) = γ a b


theorem respects_of_subset {p : X} {U : Opens X} {RU : ComponentRealizer U S p}
  (hU : γ.respects_realizer RU) {V : Opens X} (RV : ComponentRealizer V S p) (hVU : V ≤ U) :
    γ.respects_realizer RV :=
  fun hqV a b ↦ have h := sidesAtTransfer_eq_of_subset RU RV hVU hqV
    congr_arg₂ map (h a) (h b) |>.trans (hU (hVU hqV) a b)


def isLocallyConsistent : Prop :=
  ∀ {p : X}, ∃ (U : Opens X) (R : ComponentRealizer U S p), γ.respects_realizer R


theorem has_respected_realizer_basis (hγ : γ.isLocallyConsistent)
  (realizer_basis : has_realizer_basis S) {p : X} {U : Opens X} (hpU : p ∈ U) :
    ∃ (V : Opens X) (R : ComponentRealizer V S p), p ∈ V ∧ V ≤ U ∧ γ.respects_realizer R :=
  let ⟨V, RV, hV⟩ := hγ (p := p)
  let ⟨W, RW, hpW, hWUV⟩ := realizer_basis (p := p) (U := U ⊓ V) ⟨hpU, RV.1⟩
  let ⟨hWU, hWV⟩ := le_inf_iff.mp hWUV
  ⟨W, RW, hpW, hWU, γ.respects_of_subset hV RW hWV⟩


def closure_range : Subgroup G := Subgroup.closure
  {P | ∃ (p : X) (a b : SidesAt S p), γ a b = P}




end GluingPattern


end Portal
