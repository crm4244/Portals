import PortalTheory.Transport
import PortalTheory.GeneralizedMultiset



namespace Portal


variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
variable {F : Set (PortalMap X Y)} {S : Set Y}




noncomputable def quattle (γ : GluingPattern S (Equiv.Perm F))
  {p : X} (a b : SidesAt (𝒮 F S) p) : GeneralizedMultiset (Equiv.Perm F) :=
    GeneralizedMultiset.of_function fun f : relevant_portal_maps F p ↦
      recommendation_map γ (p := ⟨p, f.2⟩) a b



variable (γ : GluingPattern S (Equiv.Perm F))
variable (Γ : GeneralizedMultiset (Equiv.Perm F) → Equiv.Perm F)


class CombineTrans : Prop where
  trans : ∀ {p : X} (a b c : SidesAt (𝒮 F S) p),
    Γ (quattle γ a b) * Γ (quattle γ b c) = Γ (quattle γ a c)


variable [CombineTrans γ Γ]

noncomputable def combinedGluingPattern : GluingPattern (𝒮 F S) (Equiv.Perm F) :=
  { map a b := Γ (quattle γ a b), trans := ‹CombineTrans γ Γ›.trans}

noncomputable abbrev 𝒢 := combinedGluingPattern γ Γ



variable [TransportSymmetry (𝒢 γ Γ).closure_range]



theorem simultaneous_transport
  (P : (𝒢 γ Γ).closure_range) {p : 𝒰 F} (a b : SidesAt (𝒮 F S) p) :
    𝒢 γ Γ (SidesAt.transport' P a) (SidesAt.transport' P b) = 𝒢 γ Γ a b := by
  apply congr_arg Γ <| Quotient.eq.mpr _ |>.symm
  use {
    toFun f := ⟨P.1 f.1, transport_relevant P f⟩
    invFun f := ⟨P⁻¹.1 f.1, by
      have h : p = transport P⁻¹ (transport P p) := by
        simp [transport_mul_apply _ _ _ |>.symm, transport_one_apply]
      exact Subtype.coe_eq_iff.mpr ⟨pretransport_mem _ _, h⟩ ▸ transport_relevant P⁻¹ f⟩
    left_inv f := Subtype.eq <| P.1.symm_apply_apply f.1
    right_inv f := Subtype.eq <| P.1.apply_symm_apply f.1 }
  exact funext fun f ↦ γ.congr_map
    ((P.1 f.1).1.2.injective <| pretransport_eq_transportOf P f.2 |>.symm.trans <|
      (P.1 f.1).1.inv_right ⟨pretransport P p, transport_relevant P f⟩ |>.symm)
    (rusto_transport_eq P <| a.2.symm ▸ f.2) (rusto_transport_eq P <| b.2.symm ▸ f.2)


private noncomputable abbrev getSymmetricGluingPerm {p} (a b : SidesAt (𝒮 F S) p) :
  (𝒢 γ Γ).closure_range :=
    ⟨𝒢 γ Γ a b, Subgroup.mem_closure_of_mem ⟨_, _, _, rfl⟩⟩


def matspace_rel (a b : Sides (𝒮 F S)) : Prop :=
  a = b ∨ ∃ (ha : a.center ∈ 𝒰 F) (a' : Sides (𝒮 F S)) (ha' : a'.center = a.center),
    a'.transport' (getSymmetricGluingPerm γ Γ ⟨a, rfl⟩ ⟨a', ha'⟩) (ha' ▸ ha) = b


instance instEquivalenceMatSpaceRel : Equivalence <| matspace_rel γ Γ where
  refl a := Or.inl rfl

  symm {a _} hab := by
    apply Or.elim hab (Or.inl ·.symm)
    intro ⟨ha, a', ha', hb⟩
    cases hb
    apply Or.inr
    use Sides.center_mem_of_restricted _
    let P := getSymmetricGluingPerm γ Γ ⟨a, rfl⟩ ⟨a', ha'⟩
    use a.transport' P ha
    use (by
      simp only [Sides.center_transport'_comm,
        Sides.center_transport_comm, Sides.restrict_comm]
      exact congr_arg (Subtype.val ∘ transport _) (Subtype.mk_eq_mk.mpr ha'.symm))

    apply Sides.transport'_mul _ _ _ _ |>.symm.trans
    simp only [P, MulMemClass.mk_mul_mk]
    simp only [simultaneous_transport γ Γ P (p := ⟨a.center, ha⟩) ⟨a, rfl⟩ ⟨a', ha'⟩ |>.symm, P,
      SidesAt.transport']
    --simp [(𝒢 γ Γ).congr_map _ _]







    sorry

  trans {a _ _} hab hbc := by
    apply Or.elim hab (· ▸ hbc)
    intro ⟨ha, a', ha', h⟩
    cases h
    apply Or.elim hbc (· ▸ hab)
    intro ⟨hb, b', hb', h⟩
    cases h
    apply Or.inr
    use ha
    let a'' := b'.transport' (getSymmetricGluingPerm γ Γ ⟨a', ha'⟩ ⟨a, rfl⟩) (hb' ▸ hb)
    use a''
    have ha'' : a''.center = a.center := by

      --simp [Sides.center_transport_comm _, Sides.restrict_comm _ _]

      --apply Sides.center_transport'_comm _ _ _ |>.trans


      sorry
    use ha''
    apply Sides.transport'_mul _ _ _ _ |>.symm.trans
    congr



    have sim := simultaneous_transport γ Γ (getSymmetricGluingPerm γ Γ ⟨a, rfl⟩ ⟨a', ha'⟩)
      (p := ⟨_, ha⟩) ⟨a', ha'⟩ ⟨a'', ha''⟩
    simp only [MulMemClass.mk_mul_mk, (𝒢 γ Γ).trans, a'', sim.symm, SidesAt.transport']
    apply Subtype.eq
    apply (𝒢 γ Γ).congr_map _ _ _
    · simp [Sides.center_transport'_comm, Sides.center_transport_comm _, Sides.restrict_comm _ _]
      exact congr_arg _ <| Subtype.eq ha'.symm
    · exact rfl
    · simp [Sides.transport']
      -- need Sides.transport_mul or Sides.transport'_mul
      -- need Sides.transport_one
      sorry



def MatSpace : Type _ := Quotient {
  r := matspace_rel γ Γ
  iseqv := instEquivalenceMatSpaceRel γ Γ
}


namespace MatSpace


instance : TopologicalSpace (MatSpace γ Γ) := instTopologicalSpaceQuotient

-- woohoo!!!



end MatSpace

end Portal
