import Portals.CategoryTheory.MaterialSpace
import Portals.CategoryTheory.Rollercoaster


open Portal TopologicalSpace


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {F : Set (PortalMap X Y)} {S : Set Y}
variable {γ : GluingPattern S (Equiv.Perm F)}
variable {Γ : GeneralizedMultiset (Equiv.Perm F) → Equiv.Perm F}
variable (𝒢_trans : ∀ {p : X} (a b c : Sides.at_point (𝒮 F S) p),
  Γ (quattle γ a b) * Γ (quattle γ b c) = Γ (quattle γ a c))
variable (transport_symmetry : ∀ P (f g : F) (q : X) (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
  transportOf P ⟨q, hf⟩ = transportOf P ⟨q, hg⟩)


def Chariot (p : X) := {x : (Sides.at_point (𝒮 F S) p → Equiv.Perm F) //
  ∀ a b : Sides.at_point (𝒮 F S) p, x a * combinedGluingPattern 𝒢_trans a b = x b}


namespace Chariot

variable {p : X}




noncomputable def transfer_apply {_ : Chariot 𝒢_trans p} {x : X} {U : Opens X}
  {R : ComponentRealizer U (𝒮 F S) x} (h : combinedGluingPattern 𝒢_trans |>.respects_realizer R)
  (hp : p ∈ U) {q : X} (hq : q ∈ U) (a : Sides.at_point (𝒮 F S) p) : Chariot 𝒢_trans q :=
    ⟨fun b ↦ combinedGluingPattern 𝒢_trans
      (R.side_transfer_at hp a) (R.side_transfer_at hq b),
    fun a' b' ↦ combinedGluingPattern 𝒢_trans |>.trans _ _ _
        |>.symm.trans (congr_arg _ <| h hq a' b') |>.symm⟩


theorem transfer_apply_eq {C : Chariot 𝒢_trans p} {x : X} {U : Opens X}
  {R : ComponentRealizer U (𝒮 F S) x} (h : combinedGluingPattern 𝒢_trans |>.respects_realizer R)
  (hp : p ∈ U) {q : X} (hq : q ∈ U) (a b : Sides.at_point (𝒮 F S) p) :
    C.transfer_apply 𝒢_trans h hp hq a = C.transfer_apply 𝒢_trans h hp hq b := by

  unfold transfer_apply
  apply Subtype.eq
  simp only
  apply funext
  intro x

  sorry


noncomputable def transfer [h_nonempty : Nonempty (Sides.at_point (𝒮 F S) p)]
  {C : Chariot 𝒢_trans p} {x : X} {U : Opens X} {R : ComponentRealizer U (𝒮 F S) x}
  (h : combinedGluingPattern 𝒢_trans |>.respects_realizer R) (hp : p ∈ U) {q : X} (hq : q ∈ U) :
    Chariot 𝒢_trans q :=
  C.transfer_apply 𝒢_trans h hp hq (Classical.choice h_nonempty)


theorem transfer_eq_apply {C : Chariot 𝒢_trans p} {x : X} {U : Opens X}
  {R : ComponentRealizer U (𝒮 F S) x} (h : combinedGluingPattern 𝒢_trans |>.respects_realizer R)
  (hp : p ∈ U) {q : X} (hq : q ∈ U) (a : Sides.at_point (𝒮 F S) p) :
    C.transfer 𝒢_trans (h_nonempty := ⟨a⟩) h hp hq = C.transfer_apply 𝒢_trans h hp hq a :=
  transfer_apply_eq _ _ _ _ _ _


open Classical in noncomputable def toMatSpace_apply
  (C : Chariot 𝒢_trans p) (a : Sides.at_point (𝒮 F S) p) : MatSpace 𝒢_trans transport_symmetry :=
    if h : p ∈ 𝒰 F then ⟦Sides.lift_at (Sides.transport_at
      transport_symmetry (C.1 a) (Sides.restricted_at_of_at h a))⟧
    else ⟦a⟧


theorem toMatSpace_apply_eq (C : Chariot 𝒢_trans p) (a b : Sides.at_point (𝒮 F S) p) :
  C.toMatSpace_apply 𝒢_trans transport_symmetry a =
    C.toMatSpace_apply 𝒢_trans transport_symmetry b := by

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


noncomputable def toMatSpace [h : Nonempty (Sides.at_point (𝒮 F S) p)]
  (C : Chariot 𝒢_trans p) : MatSpace 𝒢_trans transport_symmetry :=
    C.toMatSpace_apply 𝒢_trans transport_symmetry (Classical.choice h)


theorem toMatSpace_eq_apply (C : Chariot 𝒢_trans p) (a : Sides.at_point (𝒮 F S) p) :
  C.toMatSpace 𝒢_trans transport_symmetry (h := ⟨a⟩) =
    C.toMatSpace_apply 𝒢_trans transport_symmetry a :=
  toMatSpace_apply_eq _ _ _ _ _



end Chariot
