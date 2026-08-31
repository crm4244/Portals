import Portals.CategoryTheory.MaterialSpace
--import Portals.CategoryTheory.Rollercoaster


open Portal TopologicalSpace

variable {Y : Type*} [TopologicalSpace Y] {S : Set Y}




class Chariot {G : Type*} [Group G] (γ : GluingPattern S G) (p : Y) where
  map : SidesAt S p → G
  chariotCondition : ∀ a b : SidesAt S p, map a * γ a b = map b


instance {G : Type*} [Group G] (γ : GluingPattern S G) (p : Y) : CoeFun (Chariot γ p)
  (fun _ ↦ SidesAt S p → G) where
    coe C := C.map



namespace Chariot


section transfer

variable {G : Type*} [Group G] {γ : GluingPattern S G}
variable {p : Y} {C : Chariot γ p}
variable {hub : Y} {U : Opens Y} {R : ComponentRealizer U S hub}


noncomputable def transfer_apply (hR : γ.respects_realizer R)
  (hp : p ∈ U) {q : Y} (hq : q ∈ U) (a : SidesAt S p) : Chariot γ q :=
    ⟨fun b ↦ C a * γ (R.sidesAtTransfer hp a) (R.sidesAtTransfer hq b),
    fun a' b' ↦ mul_assoc _ _ _ |>.trans <| congr_arg _ <|
      (γ.trans _ _ _).symm.trans (congr_arg _ <| hR hq a' b') |>.symm⟩


theorem transfer_apply_eq (hR : γ.respects_realizer R)
  (hp : p ∈ U) {q : Y} (hq : q ∈ U) (a b : SidesAt S p) :
    C.transfer_apply hR hp hq a = C.transfer_apply hR hp hq b :=
  mk.congr_simp _ _ (funext fun _ ↦ by
    simp only [← C.2 b a, ← hR hp b a, mul_assoc]
    exact congr_arg (C b * ·) <| γ.trans _ _ _) _


noncomputable def transfer [h_nonempty : Nonempty (SidesAt S p)]
  (hR : γ.respects_realizer R) (hp : p ∈ U) {q : Y} (hq : q ∈ U) :
    Chariot γ q :=
  C.transfer_apply hR hp hq (Classical.choice h_nonempty)


theorem transfer_eq_apply (hR : γ.respects_realizer R)
  (hp : p ∈ U) {q : Y} (hq : q ∈ U) (a : SidesAt S p) :
    C.transfer (h_nonempty := ⟨a⟩) hR hp hq = C.transfer_apply hR hp hq a :=
  transfer_apply_eq _ _ _ _ _


end transfer





variable {X : Type*} [TopologicalSpace X]
variable {F : Set (PortalMap X Y)} {γ : GluingPattern S (Equiv.Perm F)}
variable {Γ : GeneralizedMultiset (Equiv.Perm F) → Equiv.Perm F} [CombineTrans γ Γ]
variable {p : X} {C : Chariot (𝒢 γ Γ) p}


def allSymmetric (C : Chariot (𝒢 γ Γ) p) : Prop :=
  ∀ a, C a ∈ (𝒢 γ Γ).closure_range


theorem allSymmetric_transfer (hC : C.allSymmetric) [h_nonempty : Nonempty (SidesAt (𝒮 F S) p)]
  {hub : X} {U : Opens X} {R : ComponentRealizer U (𝒮 F S) hub}
  (hR : (𝒢 γ Γ).respects_realizer R) (hp : p ∈ U) {q : X} (hq : q ∈ U) :
    (C.transfer hR hp hq).allSymmetric :=
  fun _ ↦ (𝒢 γ Γ).closure_range.mul_mem (hC _) (Subgroup.mem_closure_of_mem ⟨_, _, _, rfl⟩)


variable [TransportSymmetry (𝒢 γ Γ).closure_range] (hC : C.allSymmetric)


open Classical in noncomputable def toMatSpace_apply (a : SidesAt (𝒮 F S) p) :
  MatSpace γ Γ :=
    if h : p ∈ 𝒰 F then ⟦Sides.transport' ⟨C a, hC a⟩ a.1 (a.2.symm ▸ h)⟧
    else ⟦a.1⟧


theorem toMatSpace_apply_eq (a b : SidesAt (𝒮 F S) p) :
  C.toMatSpace_apply hC a = C.toMatSpace_apply hC b := by

  apply by_cases (p := p ∈ 𝒰 F)
  · intro h
    unfold toMatSpace_apply
    rw [dif_pos h, dif_pos h]
    apply Quotient.eq.mpr
    right
    use a.1.center_transport'_mem _ (a.2.symm ▸ h)
    use b.1.transport' ⟨C a, hC a⟩ (b.2.symm ▸ h)
    use (by
      simp only [Sides.center_transport'_comm, Sides.center_transport_comm, Sides.restrict_comm]
      exact congr_arg (Subtype.val ∘ transport _) <| Subtype.mk_eq_mk.mpr <| b.2.trans a.2.symm)

    rw [Sides.transport'_mul _ _ _ _ |>.symm]
    simp only [MulMemClass.mk_mul_mk]
    congr
    apply C.chariotCondition a b |>.symm.trans (congr_arg (C a * ·) _) |>.symm
    have sim := simultaneous_transport γ Γ ⟨C a, hC a⟩ a.restrict b.restrict
    simp [SidesAt.transport, SidesAt.lift, SidesAt.restrict, Sides.lift_restrict] at sim
    have meep : pretransport ⟨C a, hC a⟩ ⟨p, h⟩ =
      (Sides.transport ⟨C a, hC a⟩ (a.1.restrict <| a.2.symm ▸ h)).lift.center := by
        simp only [Sides.lift_comm, Sides.center_transport_comm,
          Sides.restrict_comm a.1 _, transport, a.2]
    exact sim.symm.trans <| (𝒢 γ Γ).congr_map meep
      (Subtype.heq_iff_coe_eq (fun _ ↦ ⟨(·.trans meep), (·.trans meep.symm)⟩) |>.mpr rfl)
      (Subtype.heq_iff_coe_eq (fun _ ↦ ⟨(·.trans meep), (·.trans meep.symm)⟩) |>.mpr rfl)

  · intro h
    unfold toMatSpace_apply
    rw [dif_neg h, dif_neg h]
    exact congr_arg (Quotient.mk _ ∘ Subtype.val) <|
      SidesAt.subsingleton_of_not_mem (h <| 𝒮_subset_𝒰 F S ·) |>.allEq a b


noncomputable def toMatSpace [h : Nonempty (SidesAt (𝒮 F S) p)] :
  MatSpace γ Γ :=
    C.toMatSpace_apply hC (Classical.choice h)


theorem toMatSpace_eq_apply (a : SidesAt (𝒮 F S) p) :
  C.toMatSpace hC (h := ⟨a⟩) =
    C.toMatSpace_apply hC a :=
  toMatSpace_apply_eq hC _ a



end Chariot
