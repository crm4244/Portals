import Mathlib.Algebra.Group.Subgroup.Lattice
import PortalTheory.Recommendations




-- obviously this does not belong here
theorem Continuous.subtype_mk_self_mk_val_val {X : Type*} [TopologicalSpace X]
  {Y : Type*} [TopologicalSpace Y] {p : X → Prop} {q : Y → Prop}
  {r : Subtype q → Prop} {s : Y → Prop} {f : Subtype s → X} (hf : Continuous f)
  (hs : ∀ x : Subtype r, s x) (hq : ∀ x : Subtype r, p <| f ⟨x, hs x⟩) :
    Continuous fun x : Subtype r ↦ (⟨f ⟨x, hs x⟩, hq x⟩ : Subtype p) :=
  (hf.comp <| continuous_subtype_val.subtype_map fun x hx ↦ hs ⟨x, hx⟩).subtype_mk hq




namespace Portal

open Set


variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]
abbrev 𝒰 (F : Set (PortalMap X Y)) : TopologicalSpace.Opens X :=
  ⟨⋃ f : F, f.1.range, isOpen_iUnion (·.1.2.isOpen_range)⟩

variable {F : Set (PortalMap X Y)}








theorem range_subset_𝒰 (f : F) : f.1.range ⊆ 𝒰 F := fun _ h ↦ mem_iUnion.mpr ⟨f, h⟩

def inclusion_range_𝒰 (f : F) : f.1.range → 𝒰 F := inclusion <| range_subset_𝒰 f

theorem union_range_inclusion_eq_univ : ⋃ f : F, range (inclusion_range_𝒰 f) = univ :=
  eq_univ_of_univ_subset fun x _ ↦ let ⟨f, hf⟩ := (mem_iUnion.mp x.2)
    mem_iUnion.mpr ⟨f, range_inclusion (range_subset_𝒰 f) ▸ mem_setOf_eq ▸ hf⟩

theorem mem_range_of_range_inclusion {f : F} (x : range <| inclusion_range_𝒰 f) :
  x.1.1 ∈ f.1.range :=
    let ⟨_, ⟨_, y, rfl⟩, rfl⟩ := x; ⟨y, rfl⟩




noncomputable def transportOf (P : Equiv.Perm F) {f : F} (p : f.1.range) : X :=
  P f |>.1 <| f.1.inv p


theorem transportOf_mem_𝒰 (P : Equiv.Perm F) {f : F} (p : f.1.range) :
  transportOf P p ∈ 𝒰 F :=
    range_subset_𝒰 (P f) <| mem_range_self _


theorem continuous_transportOf (P : Equiv.Perm F) (f : F) :
  Continuous (transportOf P (f := f)) :=
    P f |>.1.2.continuous.comp <| continuous_subtype_val.comp f.1.homeomorph.continuous_symm




class TransportSymmetry (symmetricPerms : Subgroup (Equiv.Perm F)) : Prop where
  symmetry : ∀ (P : symmetricPerms) (f g : F) (q : X) (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
    transportOf P.1 ⟨q, hf⟩ = transportOf P.1 ⟨q, hg⟩


variable {symmetricPerms : Subgroup (Equiv.Perm F)}
variable [TransportSymmetry symmetricPerms]
variable (P Q : symmetricPerms)


noncomputable def pretransport (x : 𝒰 F) : X :=
  iUnionLift _ _ (‹TransportSymmetry symmetricPerms›.symmetry P) _ subset_rfl x


theorem pretransport_mem (x : 𝒰 F) :
  pretransport P x ∈ 𝒰 F :=
    mem_iUnion_of_mem _ <| mem_range_self _


theorem pretransport_eq_transportOf {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  pretransport P p = transportOf P.1 ⟨p, hp⟩ :=
    iUnionLift_of_mem _ _


noncomputable def transport (x : 𝒰 F) : 𝒰 F :=
  ⟨pretransport P x, pretransport_mem P x⟩


theorem transport_eq_transportOf {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  transport P p = ⟨_, transportOf_mem_𝒰 P.1 ⟨p, hp⟩⟩ :=
    Subtype.mk_eq_mk.mpr <| iUnionLift_of_mem _ _


theorem val_transport_mem_range {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  ↑(transport P p) ∈ (P.1 f).1.range :=
    let ⟨y, h⟩ := hp; ⟨y, by
    rw [transport_eq_transportOf P ⟨y, h⟩]
    exact congr_arg (P.1 f).1 <| f.1.2.injective <| h.trans <| f.1.inv_right ⟨p.1, y, h⟩ |>.symm⟩


theorem transport_mul_apply (x : 𝒰 F) :
  transport (P * Q) x =
    transport P (transport Q x) := by

  let f : F := Classical.choose <| mem_iUnion.mp x.2
  let g := Q.1 f
  have hx : x.1 ∈ f.1.range := Classical.choose_spec <| mem_iUnion.mp x.2

  let y := transport Q x
  have hy : y.1 ∈ g.1.range := exists_apply_eq_apply g.1 _

  rw [transport_eq_transportOf P hy]
  rw [transport_eq_transportOf (P * Q) hx]

  apply Subtype.mk_eq_mk.mpr <| congr_arg (P.1 g).1 <| g.1.2.injective _
  rw [g.1.inv_right]
  unfold y
  simp only
  rw [transport_eq_transportOf Q hx]
  rfl




theorem transport_mul : transport (P * Q) = transport P ∘ transport Q :=
  funext <| transport_mul_apply P Q


theorem transport_one_apply (x : 𝒰 F) : transport (symmetricPerms := symmetricPerms) 1 x = x := by
  rw [transport_eq_transportOf 1 <| Classical.choose_spec <| mem_iUnion.mp x.2]
  exact Subtype.mk_eq_mk.mpr <| PortalMap.inv_right _ _


theorem transport_one : transport (symmetricPerms := symmetricPerms) 1 = id :=
  funext fun x ↦ transport_one_apply x


theorem continuous_transport : Continuous (transport P) :=
  continuous_of_continuousOn_iUnion_of_isOpen
    (fun f ↦ continuousOn_iff_continuous_restrict.mpr <| continuous_transportOf P f
      |>.subtype_mk_self_mk_val_val _ _ |>.congr
        fun x ↦ transport_eq_transportOf P
          (mem_range_of_range_inclusion x) |>.symm)
    (fun f ↦ f.1.2.isOpen_range.isOpenMap_inclusion (range_subset_𝒰 f) |>.isOpen_range)
    union_range_inclusion_eq_univ



theorem transport_inv_left (x : ↑(𝒰 F)) :
  transport P⁻¹ (transport P x) = x :=
    transport_mul_apply _ _ _ |>.symm.trans <|
      inv_mul_cancel P ▸ transport_one_apply (symmetricPerms := symmetricPerms) x


theorem transport_inv_right (x : ↑(𝒰 F)) :
  transport P (transport P⁻¹ x) = x :=
    transport_inv_left P⁻¹ x


noncomputable def homeomorphTransport : 𝒰 F ≃ₜ 𝒰 F where
  toFun := transport P
  invFun := transport P⁻¹
  left_inv := transport_inv_left P
  right_inv := transport_inv_right P
  continuous_toFun := continuous_transport P
  continuous_invFun := continuous_transport P⁻¹


theorem 𝒮_subset_𝒰 (F : Set (PortalMap X Y)) (S : Set Y) : 𝒮 F S ⊆ 𝒰 F :=
  fun _ ⟨_, ⟨f, rfl⟩, h⟩ ↦ match h with
  | ⟨y, _, hy⟩ => mem_iUnion.mpr ⟨f, mem_range.mpr ⟨y, hy⟩⟩


abbrev 𝒮' (F : Set (PortalMap X Y)) (S : Set Y) := Sides.restrict_surface (𝒮 F S) (𝒰 F)

/-
theorem transport_mem_𝒮'_of_mem {S : Set Y} (P : symmetricPerms) {x : 𝒰 F} :
  x ∈ 𝒮' F S →
    transport P x ∈ 𝒮' F S :=
  fun ⟨_, ⟨f, rfl⟩, y, hy, hf⟩ ↦
    mem_preimage.mpr <| mem_iUnion.mpr ⟨P.1 f, ⟨y, hy, by
      rw [transport_eq_transportOf P ⟨y, hf⟩]
      exact congr_arg (P.1 f).1 <| f.1.2.injective <| hf.trans <| f.1.inv_right ⟨x, y, hf⟩ |>.symm⟩⟩
-/
/-
theorem image_transport_𝒮'_eq (S : Set Y) (P : Equiv.Perm F) :
  transport transport_symmetry P '' 𝒮' F S = 𝒮' F S :=
  Subset.antisymm
    (fun _ ⟨_, hmem, heq⟩ ↦ heq.symm ▸ transport_mem_of_mem transport_symmetry P hmem)
    (fun x h ↦ ⟨_, transport_mem_of_mem transport_symmetry P.symm h,
      instHomeomorphTransport transport_symmetry P |>.right_inv x⟩)
-/

variable {S : Set Y}

namespace Sides



noncomputable def transport : Sides (𝒮' F S) → Sides (𝒮' F S) :=
  map (f := Portal.transport P) (homeomorphTransport P).isEmbedding



@[simp] theorem center_transport_comm (σ : Sides (𝒮' F S)) :
  (σ.transport P).center = Portal.transport P σ.center := map_comm _ _


@[simp] theorem center_transport_mem (σ : Sides (𝒮' F S)) :
  (σ.transport P).center.1 ∈ 𝒰 F :=
    σ.center_transport_comm P ▸ pretransport_mem P σ.center


theorem transport_mul (σ : Sides (𝒮' F S)) :
  σ.transport (P * Q) = (σ.transport P).transport Q := by

    sorry


variable (σ : Sides (𝒮 F S)) (hσ : σ.center ∈ 𝒰 F := by assumption)


noncomputable def transport' : Sides (𝒮 F S) :=
  σ.restrict.transport P |>.lift


@[simp] theorem center_transport'_comm :
  (σ.transport' P).center = (σ.restrict.transport P).center :=
    σ.restrict.transport P |>.lift_comm


@[simp] theorem center_transport'_mem : (σ.transport' P).center ∈ 𝒰 F :=
  σ.center_transport'_comm P ▸ σ.restrict.center_transport_mem P


theorem transport'_mul : σ.transport' (P * Q) =
  (σ.transport' P).transport' Q (σ.center_transport'_mem Q) :=
    congr_arg lift <| restrict_lift (X := X) _ ▸ σ.restrict.transport_mul P Q


end Sides


noncomputable def SidesAt.transport {p : 𝒰 F} :
  SidesAt (𝒮' F S) p → SidesAt (𝒮' F S) (Portal.transport P p) :=
    fun σ ↦ ⟨σ.1.transport P, mem_setOf.mpr <|
      σ.1.center_transport_comm P |>.trans <| σ.2.symm ▸ rfl⟩


noncomputable def SidesAt.transport' {p : 𝒰 F} (σ : SidesAt (𝒮 F S) p) :
  SidesAt (𝒮 F S) (Portal.transport P p) :=
    ⟨Sides.transport' P σ.1 <| σ.2.symm ▸ p.2, sorry⟩





theorem transport_relevant {p : 𝒰 F} (f : relevant_portal_maps F p) :
  pretransport P p ∈ (P.1 f.1 |>.1.range) :=
    let ⟨y, hy⟩ := f.2; ⟨y,
      (congr_arg (P.1 f.1).1 <| f.1.1.2.injective <| hy.trans <|
        f.1.1.inv_right ⟨p, f.2⟩ |>.symm).trans <|
      pretransport_eq_transportOf P f.2 |>.symm⟩



theorem rusto_transport_eq {a : Sides (𝒮 F S)} {f : F} (hf : a.center ∈ f.1.range) :
    restricted_union_side_to_original (a.restrict (U := f.1.opens_range) hf) =
    restricted_union_side_to_original (a.restrict (range_subset_𝒰 f hf)
      |>.transport P |>.lift.restrict (U := (P.1 f).1.opens_range)
      ((Sides.lift_comm _ |>.trans <| congr_arg Subtype.val <|
        Sides.center_transport_comm P _) ▸
        (val_transport_mem_range P <| a.restrict_comm (range_subset_𝒰 f hf) ▸ hf))) :=
  by sorry







end Portal
