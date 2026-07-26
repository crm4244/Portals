import Portals.CategoryTheory.Recommendations
import Portals.CategoryTheory.GeneralizedMultiset


universe u v

namespace Portal



variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
abbrev 𝒰 (F : Set (PortalMap Y X)) : Set X := ⋃ f : F, f.1.range

variable {F : Set (PortalMap Y X)}




section transport

open Set



theorem range_subset_𝒰 (f : F) : f.1.range ⊆ 𝒰 F := fun _ h ↦ mem_iUnion.mpr ⟨f, h⟩

def inclusion_range_𝒰 (f : F) : f.1.range → 𝒰 F := inclusion <| range_subset_𝒰 f

theorem mem_range_of_range_inclusion {f : F} (x : range <| inclusion_range_𝒰 f) :
  x.1.1 ∈ f.1.range :=
    let ⟨_, ⟨_, y, rfl⟩, rfl⟩ := x; mem_range.mpr ⟨y, rfl⟩



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


noncomputable def transport (P : Equiv.Perm F) (x : 𝒰 F) : 𝒰 F :=
  ⟨pretransport transport_symmetry P x, pretransport_mem transport_symmetry P x⟩


theorem transport_eq_transportOf (P : Equiv.Perm F) {p : 𝒰 F} {f : F} (hp : p.1 ∈ f.1.range) :
  transport transport_symmetry P p = ⟨_, transportOf_mem_𝒰 P ⟨p, hp⟩⟩ :=
    Subtype.mk_eq_mk.mpr <| iUnionLift_of_mem _ _



theorem transport_mul_apply (P Q : Equiv.Perm F) (x : 𝒰 F) :
  transport transport_symmetry (P * Q) x =
    transport transport_symmetry P (transport transport_symmetry Q x) := by

  let f : F := Classical.choose <| mem_iUnion.mp x.2
  let g := Q f
  have hx : x.1 ∈ f.1.range := Classical.choose_spec <| mem_iUnion.mp x.2

  let y := transport transport_symmetry Q x
  have hy : y.1 ∈ g.1.range := mem_range.mpr <| exists_apply_eq_apply g.1 _

  rw [transport_eq_transportOf transport_symmetry P hy]
  rw [transport_eq_transportOf transport_symmetry (P * Q) hx]

  apply Subtype.mk_eq_mk.mpr <| congr_arg (P g).1 <| g.1.2.injective _
  rw [g.1.isRightInverse_invRange]
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
  exact Subtype.mk_eq_mk.mpr <| PortalMap.isRightInverse_invRange _ _


theorem transport_one : transport transport_symmetry 1 = id :=
  funext fun x ↦ transport_one_apply transport_symmetry x


theorem continuous_transport (P : Equiv.Perm F) : Continuous (transport transport_symmetry P) :=
  continuous_of_continuousOn_iUnion_of_isOpen
    (fun f ↦ continuousOn_iff_continuous_restrict.mpr <| (continuous_transportOf P f |>.comp
      <| continuous_subtype_val.comp continuous_subtype_val |>.subtype_mk _).subtype_mk _ |>.congr
      fun x : range <| inclusion_range_𝒰 f ↦ transport_eq_transportOf transport_symmetry P
        (mem_range_of_range_inclusion x) |>.symm)
    (fun f ↦ (f.1.2.isOpen_range.isOpenMap_inclusion <| range_subset_𝒰 f).isOpen_range)
    (image_val_injective <| (image_val_iUnion.trans <| congr_arg iUnion <| funext fun f ↦
      image_univ.symm ▸ image_image Subtype.val (inclusion_range_𝒰 f) univ |>.trans <|
        image_univ.trans <| Subtype.range_coe_subtype.trans setOf_mem_eq).trans <|
      Subtype.coe_image_univ (𝒰 F) |>.symm)


noncomputable instance instHomeomorphTransport (P : Equiv.Perm F) : Homeomorph (𝒰 F) (𝒰 F) where
  toFun := transport transport_symmetry P
  invFun := transport transport_symmetry P.symm
  left_inv := fun x ↦ (transport_mul_apply _ _ _ x).symm ▸ P.symm_mul ▸
    transport_one_apply transport_symmetry x
  right_inv := fun x ↦ (transport_mul_apply _ _ _ x).symm ▸ P.mul_symm ▸
    transport_one_apply transport_symmetry x
  continuous_toFun := continuous_transport transport_symmetry P
  continuous_invFun := continuous_transport transport_symmetry P.symm


theorem 𝒮_subset_𝒰 (F : Set (PortalMap Y X)) (S : Set Y) : 𝒮 F S ⊆ 𝒰 F :=
  fun _ ⟨_, ⟨f, rfl⟩, h⟩ ↦ match (mem_image f.1 S _).mp h with
  | ⟨y, _, hy⟩ => mem_iUnion.mpr ⟨f, mem_range.mpr ⟨y, hy⟩⟩

abbrev 𝒮' (F : Set (PortalMap Y X)) (S : Set Y) := Sides.restrict_surface (𝒮 F S) (𝒰 F)


theorem transport_image_𝒮'_eq_self (S : Set Y) (P : Equiv.Perm F) :
  transport transport_symmetry P '' 𝒮' F S = 𝒮' F S := by
    apply Subset.antisymm
    · intro _ ⟨⟨_, _, ⟨f, rfl⟩, y, rfl⟩, ⟨s, hs1, hs2⟩, h⟩

      --rw [h.symm]
      apply mem_image _ _ _ |>.mpr
      use ⟨transport transport_symmetry P ⟨s, 𝒮_subset_𝒰 F S s.2⟩, by
        use sorry

        sorry⟩





      sorry
    · intro _ _

      sorry


variable {S : Set Y}



noncomputable def Sides.transport (P : Equiv.Perm F) : Sides (𝒮' F S) → Sides (𝒮' F S) :=
  transport_image_𝒮'_eq_self transport_symmetry S P ▸ Sides.map
    (instHomeomorphTransport transport_symmetry P).isOpenEmbedding



theorem Sides.transport_center_comm (P : Equiv.Perm F) (σ : Sides (𝒮' F S)) :
  Portal.transport transport_symmetry P σ.center =
    (σ.transport transport_symmetry P).center := by

  sorry


noncomputable def Sides.tranport_at (P : Equiv.Perm F) {p : 𝒰 F} (σ : Sides.at_point (𝒮' F S) p) :
  Sides.restricted_at (𝒮 F S) (σ.1.transport transport_symmetry P).center.2 :=
    ⟨σ.1.transport transport_symmetry P, mem_setOf.mpr rfl⟩


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

variable (𝒢_isLocallyConsistent : GluingPattern.isLocallyConsistent (𝒢 γ Γ 𝒢_trans))


theorem simultaneous_transport {p : 𝒰 F} (a b : Sides.at_point (𝒮' F S) p) (P : Equiv.Perm F) :
  𝒢 γ Γ 𝒢_trans
    (Sides.lift_at <| Sides.tranport_at sorry P a)
    (Sides.lift_at <| Sides.tranport_at sorry P b) =
  𝒢 γ Γ 𝒢_trans (Sides.lift_at a) (Sides.lift_at b) := by

  sorry



end Portal
