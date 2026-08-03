import Portals.CategoryTheory.Recommendations
import Portals.CategoryTheory.GeneralizedMultiset




-- obviously this does not belong here
theorem Continuous.subtype_mk_self_mk_val_val {X : Type*} [TopologicalSpace X]
  {Y : Type*} [TopologicalSpace Y] {p : X → Prop} {q : Y → Prop}
  {r : Subtype q → Prop} {s : Y → Prop} {f : Subtype s → X} (hf : Continuous f)
  (hs : ∀ x : Subtype r, s x) (hq : ∀ x : Subtype r, p <| f ⟨x, hs x⟩) :
    Continuous fun x : Subtype r ↦ (⟨f ⟨x, hs x⟩, hq x⟩ : Subtype p) :=
  (hf.comp <| continuous_subtype_val.subtype_map fun x hx ↦ hs ⟨x, hx⟩).subtype_mk hq



namespace Portal



variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
abbrev 𝒰 (F : Set (PortalMap Y X)) : TopologicalSpace.Opens X :=
  ⟨⋃ f : F, f.1.range, isOpen_iUnion (·.1.2.isOpen_range)⟩

variable {F : Set (PortalMap Y X)}




section transport

open Set



theorem range_subset_𝒰 (f : F) : f.1.range ⊆ 𝒰 F := fun _ h ↦ mem_iUnion.mpr ⟨f, h⟩

def inclusion_range_𝒰 (f : F) : f.1.range → 𝒰 F := inclusion <| range_subset_𝒰 f

theorem union_range_inclusion_eq_univ : ⋃ f : F, range (inclusion_range_𝒰 f) = univ :=
  eq_univ_of_univ_subset fun x _ ↦ let ⟨f, hf⟩ := (mem_iUnion.mp x.2)
    mem_iUnion.mpr ⟨f, range_inclusion (range_subset_𝒰 f) ▸ mem_setOf_eq ▸ hf⟩

theorem mem_range_of_range_inclusion {f : F} (x : range <| inclusion_range_𝒰 f) :
  x.1.1 ∈ f.1.range :=
    let ⟨_, ⟨_, y, rfl⟩, rfl⟩ := x; ⟨y, rfl⟩




noncomputable def transportOf (P : Equiv.Perm F) {f : F} (p : f.1.range) : X :=
  P f |>.1 <| f.1.inv_range p


theorem transportOf_mem_𝒰 (P : Equiv.Perm F) {f : F} (p : f.1.range) :
  transportOf P p ∈ 𝒰 F :=
    range_subset_𝒰 (P f) <| mem_range_self _


theorem continuous_transportOf (P : Equiv.Perm F) (f : F) :
  Continuous (transportOf P (f := f)) :=
    P f |>.1.2.continuous.comp <| continuous_subtype_val.comp f.1.homeomorph.continuous_symm


variable (transport_symmetry : ∀ P (f g : F) (q : X) (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
  transportOf P ⟨q, hf⟩ = transportOf P ⟨q, hg⟩)


noncomputable def pretransport (P : Equiv.Perm F) (x : 𝒰 F) : X :=
  iUnionLift _ _ (transport_symmetry P) _ subset_rfl x


theorem pretransport_mem (P : Equiv.Perm F) (x : 𝒰 F) :
  pretransport transport_symmetry P x ∈ 𝒰 F :=
    mem_iUnion_of_mem _ <| mem_range_self _


theorem pretransport_eq_transportOf (P : Equiv.Perm F) {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  pretransport transport_symmetry P p = transportOf P ⟨p, hp⟩ :=
    iUnionLift_of_mem _ _


noncomputable def transport (P : Equiv.Perm F) (x : 𝒰 F) : 𝒰 F :=
  ⟨pretransport transport_symmetry P x, pretransport_mem transport_symmetry P x⟩


theorem transport_eq_transportOf (P : Equiv.Perm F) {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  transport transport_symmetry P p = ⟨_, transportOf_mem_𝒰 P ⟨p, hp⟩⟩ :=
    Subtype.mk_eq_mk.mpr <| iUnionLift_of_mem _ _


theorem val_transport_mem_range (P : Equiv.Perm F) {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  ↑(transport transport_symmetry P p) ∈ (P f).1.range :=
    let ⟨y, h⟩ := hp; ⟨y, by
    rw [transport_eq_transportOf transport_symmetry P ⟨y, h⟩]
    exact congr_arg (P f).1 <| f.1.2.injective <| h.trans <| f.1.inv_right ⟨p.1, y, h⟩ |>.symm⟩


theorem transport_mul_apply (P Q : Equiv.Perm F) (x : 𝒰 F) :
  transport transport_symmetry (P * Q) x =
    transport transport_symmetry P (transport transport_symmetry Q x) := by

  let f : F := Classical.choose <| mem_iUnion.mp x.2
  let g := Q f
  have hx : x.1 ∈ f.1.range := Classical.choose_spec <| mem_iUnion.mp x.2

  let y := transport transport_symmetry Q x
  have hy : y.1 ∈ g.1.range := exists_apply_eq_apply g.1 _

  rw [transport_eq_transportOf transport_symmetry P hy]
  rw [transport_eq_transportOf transport_symmetry (P * Q) hx]

  apply Subtype.mk_eq_mk.mpr <| congr_arg (P g).1 <| g.1.2.injective _
  rw [g.1.inv_right]
  unfold y
  simp only
  rw [transport_eq_transportOf transport_symmetry Q hx]
  rfl


theorem transport_mul (P Q : Equiv.Perm F) :
  transport transport_symmetry (P * Q) =
    transport transport_symmetry P ∘ transport transport_symmetry Q :=
  funext <| transport_mul_apply transport_symmetry P Q


theorem transport_one_apply (x : 𝒰 F) : transport transport_symmetry 1 x = x := by
  rw [transport_eq_transportOf transport_symmetry 1 <| Classical.choose_spec <| mem_iUnion.mp x.2]
  exact Subtype.mk_eq_mk.mpr <| PortalMap.inv_right _ _


theorem transport_one : transport transport_symmetry 1 = id :=
  funext fun x ↦ transport_one_apply transport_symmetry x


theorem continuous_transport (P : Equiv.Perm F) : Continuous (transport transport_symmetry P) :=
  continuous_of_continuousOn_iUnion_of_isOpen
    (fun f ↦ continuousOn_iff_continuous_restrict.mpr <| continuous_transportOf P f
      |>.subtype_mk_self_mk_val_val _ _ |>.congr
        fun x ↦ transport_eq_transportOf transport_symmetry P
          (mem_range_of_range_inclusion x) |>.symm)
    (fun f ↦ f.1.2.isOpen_range.isOpenMap_inclusion (range_subset_𝒰 f) |>.isOpen_range)
    union_range_inclusion_eq_univ


theorem transport_inv_left (P : Equiv.Perm F) (x : ↑(𝒰 F)) :
  transport transport_symmetry (Equiv.symm P) (transport transport_symmetry P x) = x :=
    (transport_mul_apply _ _ _ x).symm ▸ P.symm_mul ▸ transport_one_apply transport_symmetry x


theorem transport_inv_right (P : Equiv.Perm F) (x : ↑(𝒰 F)) :
  transport transport_symmetry P (transport transport_symmetry (Equiv.symm P) x) = x :=
    transport_inv_left transport_symmetry P.symm x


noncomputable instance instHomeomorphTransport (P : Equiv.Perm F) : Homeomorph (𝒰 F) (𝒰 F) where
  toFun := transport transport_symmetry P
  invFun := transport transport_symmetry P.symm
  left_inv := transport_inv_left transport_symmetry P
  right_inv := transport_inv_right transport_symmetry P
  continuous_toFun := continuous_transport transport_symmetry P
  continuous_invFun := continuous_transport transport_symmetry P.symm

/-
theorem 𝒮_subset_𝒰 (F : Set (PortalMap Y X)) (S : Set Y) : 𝒮 F S ⊆ 𝒰 F :=
  fun _ ⟨_, ⟨f, rfl⟩, h⟩ ↦ match h with
  | ⟨y, _, hy⟩ => mem_iUnion.mpr ⟨f, mem_range.mpr ⟨y, hy⟩⟩
-/

abbrev 𝒮' (F : Set (PortalMap Y X)) (S : Set Y) := Sides.restrict_surface (𝒮 F S) (𝒰 F)


theorem transport_mem_𝒮'_of_mem {S : Set Y} (P : Equiv.Perm F) {x : 𝒰 F} :
  x ∈ 𝒮' F S →
    transport transport_symmetry P x ∈ 𝒮' F S :=
  fun ⟨_, ⟨f, rfl⟩, y, hy, hf⟩ ↦
    mem_preimage.mpr <| mem_iUnion.mpr ⟨P f, ⟨y, hy, by
      rw [transport_eq_transportOf transport_symmetry P ⟨y, hf⟩]
      exact congr_arg (P f).1 <| f.1.2.injective <| hf.trans <| f.1.inv_right ⟨x, y, hf⟩ |>.symm⟩⟩

/-
theorem image_transport_𝒮'_eq (S : Set Y) (P : Equiv.Perm F) :
  transport transport_symmetry P '' 𝒮' F S = 𝒮' F S :=
  Subset.antisymm
    (fun _ ⟨_, hmem, heq⟩ ↦ heq.symm ▸ transport_mem_of_mem transport_symmetry P hmem)
    (fun x h ↦ ⟨_, transport_mem_of_mem transport_symmetry P.symm h,
      instHomeomorphTransport transport_symmetry P |>.right_inv x⟩)
-/

variable {S : Set Y}



noncomputable def Sides.transport (P : Equiv.Perm F) : Sides (𝒮' F S) → Sides (𝒮' F S) :=
  map <| instHomeomorphTransport transport_symmetry P |>.isOpenEmbedding



theorem Sides.transport_center_comm (P : Equiv.Perm F) (σ : Sides (𝒮' F S)) :
  (σ.transport transport_symmetry P).center =
    Portal.transport transport_symmetry P σ.center := map_comm _ _


noncomputable def Sides.tranport_at (P : Equiv.Perm F) {p : 𝒰 F} (σ : at_point (𝒮' F S) p) :
  at_point (𝒮' F S) (Portal.transport transport_symmetry P p) :=
    ⟨σ.1.transport transport_symmetry P, mem_setOf.mpr <|
      transport_center_comm transport_symmetry P σ.1 |>.trans <| σ.2.symm ▸ rfl⟩


theorem transport_relevant (P : Equiv.Perm F) {p : 𝒰 F} (f : relevant_portal_maps F p) :
  pretransport transport_symmetry P p ∈ (P f.1 |>.1.range) :=
    let ⟨y, hy⟩ := f.2; ⟨y,
      (congr_arg (P f.1).1 <| f.1.1.2.injective <| hy.trans <|
        f.1.1.inv_right ⟨p, f.2⟩ |>.symm).trans <|
      pretransport_eq_transportOf transport_symmetry P f.2 |>.symm⟩


theorem rusto_transport_eq (P : Equiv.Perm F)
  {a : Sides (𝒮 F S)} {f : F} (hf : a.center ∈ f.1.range) :
    restricted_union_side_to_original (a.restrict_of_mem (U := f.1.opens_range) hf) =
    restricted_union_side_to_original (a.restrict_of_mem (range_subset_𝒰 f hf)
      |>.transport transport_symmetry P |>.lift.restrict_of_mem (U := (P f).1.opens_range)
      ((Sides.lift_comm _ |>.trans <| congr_arg Subtype.val <|
        Sides.transport_center_comm transport_symmetry P _) ▸
        (val_transport_mem_range _ P <| a.center_restrict_comm (range_subset_𝒰 f hf) ▸ hf))) := by sorry


end transport





variable {S : Set Y} (γ : GluingPattern S (Equiv.Perm F))
variable (Γ : GeneralizedMultiset (Equiv.Perm F) → Equiv.Perm F)



noncomputable def quattle {p : X} (a b : Sides.at_point (𝒮 F S) p) :
  GeneralizedMultiset (Equiv.Perm F) :=
    GeneralizedMultiset.of_function fun f : relevant_portal_maps F p ↦
      recommendation_map γ (p := ⟨p, f.2⟩) a b


variable (𝒢_trans : ∀ {p : X} (a b c : Sides.at_point (𝒮 F S) p),
  Γ (quattle γ a b) * Γ (quattle γ b c) = Γ (quattle γ a c))



noncomputable def combinedGluingPattern : GluingPattern (𝒮 F S) (Equiv.Perm F) :=
  { map a b := Γ (quattle γ a b), trans := 𝒢_trans }

noncomputable abbrev 𝒢 := combinedGluingPattern γ Γ 𝒢_trans

--variable (𝒢_isLocallyConsistent : GluingPattern.isLocallyConsistent (𝒢 γ Γ 𝒢_trans))
variable (transport_symmetry : ∀ P (f g : F) (q : X) (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
    transportOf P ⟨q, hf⟩ = transportOf P ⟨q, hg⟩)


open GenMulti in theorem simultaneous_transport
  (P : Equiv.Perm F) {p : 𝒰 F} (a b : Sides.at_point (𝒮' F S) p) :
    𝒢 γ Γ 𝒢_trans
      (Sides.lift_at <| Sides.tranport_at transport_symmetry P a)
      (Sides.lift_at <| Sides.tranport_at transport_symmetry P b) =
    𝒢 γ Γ 𝒢_trans (Sides.lift_at a) (Sides.lift_at b) := by

  apply congr_arg Γ <| Quotient.eq.mpr _
  symm
  unfold instSetoid rel of_function
  simp only
  use {
    -- maybe build this equiv in the transport section
    toFun f := ⟨P f.1, transport_relevant transport_symmetry P f⟩
    invFun f := ⟨P.symm f.1, by
      #check f.2
      #check transport_relevant transport_symmetry P.symm ⟨_, sorry⟩
      sorry⟩
    left_inv f := Subtype.eq <| P.symm_apply_apply f.1
    right_inv f := Subtype.eq <| P.apply_symm_apply f.1
  }

  unfold Function.comp
  simp?
  apply funext
  intro f
  unfold recommendation_map GluingPattern.map recommendation_gluing_pattern GluingPattern.map
  unfold Sides.tranport_at Sides.restricted_at_of_at rusto_at_of_at
  simp

  sorry


def matSpace_rel (a b : Sides (𝒮 F S)) : Prop :=
  a = b ∨ ∃ (ha : a.center ∈ 𝒰 F) (a' : Sides (𝒮 F S)) (ha' : a'.center = a.center),
    (a'.restrict_of_mem (ha' ▸ ha) |>.transport
      transport_symmetry (𝒢 γ Γ 𝒢_trans ⟨a, rfl⟩ ⟨a', ha'⟩)).lift = b


instance instEquivalenceMatSpaceRel : Equivalence <| matSpace_rel γ Γ 𝒢_trans transport_symmetry where
  refl a := Or.inl rfl
  symm {a b} hab := by
    apply Or.elim hab (Or.inl ·.symm)
    intro ⟨ha, a', ha', hb⟩
    apply Or.inr
    use hb.symm ▸ Sides.center_mem_of_restricted _
    use a.restrict_of_mem.transport transport_symmetry (𝒢 γ Γ 𝒢_trans ⟨a, rfl⟩ ⟨a', ha'⟩) |>.lift

    use by
      rw [hb.symm]
      apply Sides.lift_comm _ |>.trans
      apply Sides.lift_comm _ |>.trans _ |>.symm
      apply congr_arg Subtype.val
      apply Sides.transport_center_comm _ _ _ |>.trans
      apply Sides.transport_center_comm _ _ _ |>.trans _ |>.symm
      apply congr_arg _
      apply Sides.center_restrict_comm _ _ |>.trans
      apply Sides.center_restrict_comm _ _ |>.trans _ |>.symm
      exact Subtype.mk_eq_mk.mpr ha'

    --rw [transport_eq_transportOf transport_symmetry _ _]
    --rw [Sides.restrict_lift _]
    --apply Subtype.mk_eq_mk.mp
    --apply Sides.restrict_injective
    --simp only
    --rw [Sides.restrict_lift]
    --rw [Sides.restrict_lift]
    --rw [← simultaneous_transport γ Γ 𝒢_trans transport_symmetry (𝒢 γ Γ 𝒢_trans ⟨a, rfl⟩ ⟨a', ha'⟩).symm]

    #check Sides.restrict_of_mem
    sorry
  trans {a b c} hab hbc := by
    apply Or.elim hab (· ▸ hbc)
    intro ⟨ha, a', ha', hb⟩
    apply Or.elim hbc (· ▸ hab)
    intro ⟨_, b', hb', hc⟩
    apply Or.inr

    sorry


instance instSetoidSides𝒮 : Setoid (Sides (𝒮 F S)) where
  r := matSpace_rel γ Γ 𝒢_trans transport_symmetry
  iseqv := instEquivalenceMatSpaceRel γ Γ 𝒢_trans transport_symmetry


def MatSpace := Quotient (instSetoidSides𝒮 γ Γ 𝒢_trans transport_symmetry)

namespace MatSpace


-- woohoo!!!



end MatSpace

end Portal
