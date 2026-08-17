import Portals.CategoryTheory.MaterialSpace
--import Portals.CategoryTheory.Rollercoaster


open Portal TopologicalSpace

variable {Y : Type*} [TopologicalSpace Y] {S : Set Y}



def Chariot {G : Type*} [Group G] (γ : GluingPattern S G) (p : Y) :=
  {x : (Sides.at_point S p → G) // ∀ a b : Sides.at_point S p, x a * γ a b = x b}



namespace Chariot



section transfer

variable {G : Type*} [Group G] (γ : GluingPattern S G)
variable {p : Y} {C : Chariot γ p}
variable {hub : Y} {U : Opens Y} {R : ComponentRealizer U S hub}


noncomputable def transfer_apply (hR : γ.respects_realizer R)
  (hp : p ∈ U) {q : Y} (hq : q ∈ U) (a : Sides.at_point S p) : Chariot γ q :=
    ⟨fun b ↦ C.1 a * γ
      (R.side_transfer_at hp a) (R.side_transfer_at hq b),
    fun a' b' ↦ mul_assoc _ _ _ |>.trans <| congr_arg _ <|
      (γ.trans _ _ _).symm.trans (congr_arg _ <| hR hq a' b') |>.symm⟩


theorem transfer_apply_eq (hR : γ.respects_realizer R)
  (hp : p ∈ U) {q : Y} (hq : q ∈ U) (a b : Sides.at_point S p) :
    C.transfer_apply γ hR hp hq a = C.transfer_apply γ hR hp hq b :=
  Subtype.eq <| funext fun _ ↦ by
    simp only [transfer_apply, ← C.2 b a, ← hR hp b a, mul_assoc]
    exact congr_arg _ <| γ.trans _ _ _


noncomputable def transfer [h_nonempty : Nonempty (Sides.at_point S p)]
  (hR : γ.respects_realizer R) (hp : p ∈ U) {q : Y} (hq : q ∈ U) :
    Chariot γ q :=
  C.transfer_apply γ hR hp hq (Classical.choice h_nonempty)


theorem transfer_eq_apply (hR : γ.respects_realizer R)
  (hp : p ∈ U) {q : Y} (hq : q ∈ U) (a : Sides.at_point S p) :
    C.transfer γ (h_nonempty := ⟨a⟩) hR hp hq = C.transfer_apply γ hR hp hq a :=
  transfer_apply_eq _ _ _ _ _ _


end transfer





variable {X : Type*} [TopologicalSpace X]
variable {F : Set (PortalMap X Y)} (γ : GluingPattern S (Equiv.Perm F))
variable (Γ : GeneralizedMultiset (Equiv.Perm F) → Equiv.Perm F) [CombineTrans γ Γ]
variable (symmetricPerms : Subgroup (Equiv.Perm F)) [TransportSymmetry symmetricPerms]
variable {p : X} {C : Chariot (𝒢 γ Γ) p}


open Classical in noncomputable def toMatSpace_apply (a : Sides.at_point (𝒮 F S) p) :
  MatSpace γ Γ symmetricPerms :=
    if h : p ∈ 𝒰 F then ⟦Sides.lift_at (Sides.transport_at
      ⟨C.1 a, (sorry : C.1 a ∈ symmetricPerms)⟩ (Sides.restricted_at_of_at h a))⟧
    else ⟦a⟧


def isWellDefined_toMatSpace : Prop := ∀ a b,
  C.toMatSpace_apply γ Γ symmetricPerms a =
  C.toMatSpace_apply γ Γ symmetricPerms b


theorem isWellDefined_toMatSpace_transfer [h_nonempty : Nonempty (Sides.at_point (𝒮 F S) p)]
  {hub : X} {U : Opens X} {R : ComponentRealizer U (𝒮 F S) hub}
  (hR : 𝒢 γ Γ |>.respects_realizer R) (hp : p ∈ U) {q : X} (hq : q ∈ U)
  (h_wellDefined : C.isWellDefined_toMatSpace γ Γ symmetricPerms) :
    C.transfer (𝒢 γ Γ) hR hp hq |>.isWellDefined_toMatSpace γ Γ symmetricPerms := by

  intro _ _
  unfold toMatSpace_apply
  if h : p ∈ 𝒰 F then
    rw [dif_pos h, dif_pos h]
    apply Quotient.eq.mpr
    apply Or.intro_right _ _
    have __ : Sides.lift_at (Sides.transport_at transport_symmetry (C.1 a)
      (Sides.restricted_at_of_at h a)) |>.1.center ∈ 𝒰 F := by
        unfold Sides.lift_at Sides.transport_at

        simp only [Sides.lift_at, Sides.transport_at]

        apply Sides.transport_center_comm transport_symmetry (C.1 a) (a.1.restrict_of_mem (by rw [a.2]; exact h)) ▸ _

        sorry

    use __

    sorry
  else
    rw [dif_neg h, dif_neg h]
    exact congr_arg _ (sorry : a.1 = b.1)


theorem toMatSpace_apply_eq (a b : Sides.at_point (𝒮 F S) p) :
  C.toMatSpace_apply γ Γ symmetricPerms a =
    C.toMatSpace_apply γ Γ symmetricPerms b :=
  sorry


noncomputable def toMatSpace [h : Nonempty (Sides.at_point (𝒮 F S) p)] :
  MatSpace γ Γ symmetricPerms :=
    C.toMatSpace_apply γ Γ  symmetricPerms (Classical.choice h)


theorem toMatSpace_eq_apply (a : Sides.at_point (𝒮 F S) p) :
  C.toMatSpace γ Γ symmetricPerms (h := ⟨a⟩) =
    C.toMatSpace_apply γ Γ symmetricPerms a :=
  toMatSpace_apply_eq _ _ _ _ _



end Chariot
