import Portals.CategoryTheory.Sides

open Portal TopologicalSpace

variable {X : Type*} [TopologicalSpace X]


def SidesAt (S : Set X) (p : X) : Type _ := { σ : Sides S // σ.center = p }


namespace SidesAt

variable {S : Set X} {p : X}


theorem subsingleton_of_not_mem {p : X} (h : p ∉ S) :
  Subsingleton (SidesAt S p) where
    allEq a b := sorry


-- the induced topology is discrete


def restricted_touchingComponent (S : Set X) {U : Set X} (hp : p ∈ U) :
    SidesAt (Sides.restrict_surface S U) ⟨p, hp⟩ → Sides.restricted_punctured_components S U := by
  --#check Subtype.restrict
  --  (fun σ : SidesAt (Sides.restrict_surface S U) ⟨p, hp⟩ ↦ σ.1.center = ⟨p, hp⟩)
  --  (Sides.touchingComponent (S := Sides.restrict_surface S U))
  sorry


variable (σ : SidesAt S p)


omit [TopologicalSpace X] in theorem center_mem_of_mem {U : Set X} (hp : p ∈ U) :
  σ.1.center ∈ U :=
    σ.2.symm ▸ hp

def lift {U : Set X} {hp : p ∈ U} (σ : SidesAt (Sides.restrict_surface S U) ⟨p, hp⟩) :
  SidesAt S p :=
    ⟨σ.1.lift, σ.1.lift_comm ▸ Subtype.coe_eq_iff.mpr ⟨hp, σ.2⟩⟩

noncomputable def restrict {U : Opens X} (hp : p ∈ U := by assumption) :
  SidesAt (Sides.restrict_surface S U) ⟨p, hp⟩ :=
    ⟨σ.1.restrict <| σ.center_mem_of_mem hp, Subtype.val_injective <|
      (congr_arg Subtype.val <| σ.1.restrict_comm <| σ.center_mem_of_mem hp).trans σ.2⟩


theorem lift_restrict {U : Opens X} (hp : p ∈ U) :
  σ.restrict.lift = σ :=
    Subtype.eq <| σ.1.lift_restrict (σ.2.symm ▸ hp)


theorem restrict_lift {U : Opens X} {hp : p ∈ U}
  (σ : SidesAt (Sides.restrict_surface S U) ⟨p, hp⟩) :
    σ.lift.restrict hp = σ :=
  Subtype.eq σ.1.restrict_lift


end SidesAt
