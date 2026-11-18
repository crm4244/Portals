import PortalTheory.MaterialSpace
import PortalTheory.Chariot
import PortalTheory.Rollercoaster.Path
import Mathlib.Topology.UnitInterval






namespace Portal
open unitInterval




abbrev Slice (X : Type*) {Y : Type*} (t : Y) := {x : X × Y // x.2 = t}

namespace Slice

variable {X : Type*} {Y : Type*}



def proj {t : Y} : Slice X t → X := fun x ↦ x.val.fst
def incl (t : Y) : X → Slice X t := fun x ↦ ⟨(x, t), rfl⟩

theorem proj_incl {t : Y} (x : X) : (incl t x).proj = x := rfl
theorem incl_proj {t : Y} (x : Slice X t) : incl t x.proj = x :=
  Subtype.coe_eq_of_eq_mk (congr_arg (x.1.1, ·) x.2) |>.symm



variable [TopologicalSpace X] [TopologicalSpace Y]


theorem continuous_proj {t : Y} : Continuous (@proj X Y t) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_incl (t : Y) : Continuous (@incl X Y t) :=
  Continuous.prodMk_left t |>.subtype_mk _


def homeomorph {t : Y} : Slice X t ≃ₜ X where
  toFun := proj
  invFun := incl t
  left_inv := incl_proj
  right_inv := proj_incl
  continuous_toFun := continuous_proj
  continuous_invFun := continuous_incl t



open Topology

theorem isEmbedding_proj {t : Y} : IsEmbedding (@proj X Y t) :=
  homeomorph.isEmbedding


theorem isEmbedding_incl (t : Y) : IsEmbedding (@incl X Y t) :=
  homeomorph.symm.isEmbedding


def incl' (t : Y) : X → X × Y := Subtype.val ∘ (@incl X Y t)


theorem isEmbedding_incl' (t : Y) : IsEmbedding (@incl' X Y t) :=
  IsEmbedding.subtypeVal.comp (isEmbedding_incl t)


def sides_at_map_incl' {S : Set (X × Y)} {t : Y} {p : X}
  (a : SidesAt (incl (X := X) t ⁻¹' ((↑) ⁻¹' S)) p) :
    SidesAt S (incl' t p) :=
  ⟨_, a.2 ▸ a.1.map_comm (S := S) (isEmbedding_incl' t)⟩
  --(Slice.isEmbedding_incl' t) a.1


end Slice



variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]



section extrude
variable (Z : Type*) [TopologicalSpace Z]

open Topology in private def extrude : PortalMap X Y → PortalMap (X × Z) (Y × Z)
  | f => ⟨(·.map f id), f.2.prodMap IsOpenEmbedding.id⟩

private theorem extrude_injective [Nonempty Z] : Function.Injective (extrude (X := X) (Y := Y) Z) :=
  fun _ _ h ↦ Subtype.eq <| funext fun y ↦ And.left <| Prod.eq_iff_fst_eq_snd_eq.mp <|
    (congr_fun <| Subtype.mk_eq_mk.mp h) (y, Classical.choice ‹Nonempty Z›)


-- use OfLeftInverse?
private noncomputable def extrude_equiv [Nonempty Z] (F : Set (PortalMap X Y)) :
  F ≃ Set.range (fun f : F ↦ extrude Z f.1) :=
    Equiv.ofInjective _ <| Subtype.restrict_injective (· ∈ F) <| extrude_injective Z


end extrude



abbrev ℱ (F : Set (PortalMap X Y)) := Set.range (fun f : F ↦ extrude I f.1)
variable {F : Set (PortalMap X Y)}

variable {S : Set (Y × I)}
variable (γ : GluingPattern S (Equiv.Perm (ℱ F)))
variable (Γ : GeneralizedMultiset (Equiv.Perm (ℱ F)) → Equiv.Perm (ℱ F))
variable [CombineTrans γ Γ] [TransportSymmetry (𝒢 γ Γ).closure_range]

#check MatSpace γ Γ



section slice_portal

variable (t : I)



abbrev Sₜ (S : Set (Y × I)) : Set Y := @Slice.incl' Y I t ⁻¹' S

noncomputable abbrev γₜ (γ : GluingPattern S (Equiv.Perm (ℱ F))) :
  GluingPattern (Sₜ t S) (Equiv.Perm F) where

  map a b := (extrude_equiv I F).permCongr.symm <|
    γ (Slice.sides_at_map_incl' a) (Slice.sides_at_map_incl' b)
  trans _ _ _ := Equiv.permCongr_symm _ ▸ Equiv.permCongr_mul _ _ _
    |>.symm.trans <| congr_arg _ <| γ.trans _ _ _

noncomputable abbrev Γₜ (Γ : GeneralizedMultiset (Equiv.Perm (ℱ F)) → Equiv.Perm (ℱ F)) :
  GeneralizedMultiset (Equiv.Perm F) → (Equiv.Perm F) :=
    fun 𝒰 ↦ (extrude_equiv I F).symm.permCongr <| Γ <| 𝒰.map
      (fun G ↦ ⟨G.index, fun i ↦ (extrude_equiv I F).permCongr (G.val i)⟩)
      (fun _ ⟨_, _⟩ ⟨h1, h2⟩ ↦ ⟨h1, funext fun i ↦
        congr_arg (extrude_equiv I F).permCongr (congr_fun h2 i)⟩)


noncomputable abbrev symmetricPermsₜ : Subgroup (Equiv.Perm F) :=
  (𝒢 γ Γ).closure_range.map (extrude_equiv I F).permCongrHom.symm.toMonoidHom



instance : CombineTrans (γₜ t γ) (Γₜ Γ) where
  trans {p} a b c := by

    have h := ‹CombineTrans γ Γ›.trans
      (Slice.sides_at_map_incl' (t := 0) a)
      (Slice.sides_at_map_incl' (t := 0) b)
      (Slice.sides_at_map_incl' (t := 0) c)

    unfold γₜ quattle recommendation_map GluingPattern.map at h ⊢
    unfold recommendation_gluing_pattern GluingPattern.map at h ⊢
    simp only at h ⊢

    --unfold HMul.hMul instHMul Mul.mul Equiv.Perm.instMul Equiv.trans
    --simp only
    --apply Equiv.ext
    --intro f
    --simp only [Equiv.Perm.coe_mul] at h ⊢
    unfold Γₜ

    unfold GeneralizedMultiset.of_function GenMulti.of_function at h ⊢
    simp only [Quotient.map_mk] at h ⊢
    rw [← Equiv.permCongr_mul]
    apply congr_arg


    simp only [Equiv.apply_symm_apply] at h ⊢




  --rw [← Equiv.permCongr_symm]



    #check Quotient.eq.mpr (by
      unfold GenMulti.instSetoid GenMulti.rel
      simp
      let e : relevant_portal_maps F p ≃ relevant_portal_maps (ℱ F) (p, 0) := by
        apply Equiv.subtypeEquiv (extrude_equiv I F)
        intro f
        unfold extrude_equiv Equiv.ofInjective Equiv.ofLeftInverse
        simp only [Equiv.coe_fn_mk]
        unfold extrude PortalMap.range
        simp only [Set.mem_range, Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ,
          and_true]

      use e
      ext f f'
      congr



      simp

      unfold e Equiv.subtypeEquiv
      unfold extrude_equiv Equiv.ofInjective Equiv.ofLeftInverse extrude Prod.map
      simp?


      sorry : GenMulti.instSetoid (Equiv.Perm (ℱ F))
        { index := relevant_portal_maps F p,
            val := fun i ↦ (extrude_equiv I F).permCongr
              (recommendation_map (γₜ t γ) (f := i.1) _ _) }
        { index := relevant_portal_maps (ℱ F) (p, 0),
            val := fun i ↦ recommendation_map (f := i.1) γ _ _ })



    sorry



instance : TransportSymmetry (X := X) (Y := Y) (𝒢 (γₜ t γ) (Γₜ Γ)).closure_range where
  symmetry P f g q hf hg := by

    let f' := extrude_equiv I F f
    let g' := extrude_equiv I F g
    let P' : (𝒢 γ Γ).closure_range := ⟨(extrude_equiv I F).permCongr P, sorry⟩

    have h_prod_mem {l : F} (hl : q ∈ l.1.range) : (q, 0) ∈ (extrude_equiv I F l).1.range :=
      ⟨(l.1.inv ⟨q, hl⟩, 0), Prod.map_apply _ _ _ _ |>.trans <|
        Prod.eq_iff_fst_eq_snd_eq.mpr ⟨l.1.inv_right ⟨q, hl⟩, rfl⟩⟩

    have h := ‹TransportSymmetry (𝒢 γ Γ).closure_range›.symmetry
      P' f' g' (q, 0) (h_prod_mem hf) (h_prod_mem hg)

    unfold transportOf at h ⊢
    unfold P' f' g' at h
    unfold extrude_equiv at h
    simp only [Equiv.ofInjective_apply, Equiv.permCongr_apply, Equiv.ofInjective_symm_apply] at h
    unfold extrude Prod.map at h
    simp only [Prod.mk.injEq] at h
    apply And.left at h

    have h_final {l : F} (hl : q ∈ l.1.range) :
      ((extrude I l.1).inv ⟨(q, 0), h_prod_mem hl⟩).1 = l.1.inv ⟨q, hl⟩ :=
        l.1.2.injective <| Eq.trans
          (by simpa only using congr_arg Prod.fst <| extrude_equiv I F l |>.1.inv_right _)
          (l.1.inv_right ⟨q, hl⟩).symm

    exact (h_final hf) ▸ (h_final hg) ▸ h







abbrev MatSpaceₜ : Type _ := MatSpace (γₜ t γ) (Γₜ Γ)






end slice_portal







open Topology TopologicalSpace



def sideSlice (S : Set (X × I)) (t : I) : Set (Sides S) := {a | a.center.2 = t}


def to_sideSlice (F : Set (PortalMap X Y)) (S : Set (Y × I)) (t : I) :
  Sides (𝒮 F (Sₜ t S)) → sideSlice (𝒮 (ℱ F) S) t :=
    Set.codRestrict (Sides.map (Y := Slice X t) IsEmbedding.subtypeVal) (sideSlice (𝒮 (ℱ F) S) t)
      (fun x ↦ congr_arg Prod.snd (x.map_comm _) |>.trans x.center.2)


noncomputable def to_sideSlice_homeomorph {t : I}
  (h_bijective : Function.Bijective (to_sideSlice F S t)) :
    Sides (𝒮 F (Sₜ t S)) ≃ₜ sideSlice (𝒮 (ℱ F) S) t :=
  ⟨Equiv.ofBijective _ h_bijective, by sorry, by sorry⟩


-- theorem to_sideSlice preserves matspace_rel
-- theorem t-projection is independent of rep


def matSlice (t : I) : Set (MatSpace γ Γ) := {m | m.out ∈ sideSlice (𝒮 (ℱ F) S) t} -- gotta Quot this out

noncomputable def to_matSlice (t : I) : MatSpaceₜ γ Γ t → matSlice γ Γ t := by
  intro m
  use Quotient.map (Sides.map (Y := Slice X t) IsEmbedding.subtypeVal) sorry m

  unfold matSlice

  sorry


def to_matSlice_homeomorph {t : I} (h_bijective : Function.Bijective (to_sideSlice F S t))
  : MatSpaceₜ γ Γ t ≃ₜ matSlice γ Γ t := sorry



variable (hγ : (𝒢 γ Γ).isLocallyConsistent)
variable (realizer_basis : has_realizer_basis (𝒮 (ℱ F) S))
variable (sidesAt_nonempty : ∀ p, Nonempty (SidesAt (𝒮 (ℱ F) S) p))




def 𝒪 : Set (Set (X × I)) :=
  {U | ∃ (hU : IsOpen U) (p : X × I) (R : ComponentRealizer ⟨U, hU⟩ (𝒮 (ℱ F) S) p),
    (𝒢 γ Γ).respects_realizer R}


omit [TransportSymmetry (𝒢 γ Γ).closure_range] in
include hγ realizer_basis in theorem 𝒪_cover (p : X × I) : ∃ U ∈ 𝒪 γ Γ, p ∈ U :=
  let ⟨⟨U, isOpen_U⟩, R, hpU, _, hU⟩ :=
    (𝒢 γ Γ).has_respected_realizer_basis hγ realizer_basis (trivial : p ∈ ⊤)
  ⟨U, ⟨isOpen_U, p, R, hU⟩, hpU⟩



-- reformatting some functions from Chariot.lean to fit with what Rollercoaster expects

private noncomputable def chariot_transfer'
  {U : 𝒪 γ Γ} (p q : U.1) (C : Chariot (𝒢 γ Γ) p) :
    Chariot (𝒢 γ Γ) q :=
  C.transfer U.2.2.choose_spec.2 p.2 q.2

private def chariot_allSymmetric_transfer'
  {U : 𝒪 γ Γ} {p q : U.1} (C : Chariot (𝒢 γ Γ) p)
  (hC : C.allSymmetric) :
    (chariot_transfer' γ Γ sidesAt_nonempty p q C ).allSymmetric :=
  C.allSymmetric_transfer hC U.2.2.choose_spec.2 p.2 q.2

-- this was written by Claude AI
noncomputable def segment (t0 t1 : I) : Path t0 t1 where
  toFun τ := Set.projIcc 0 1 zero_le_one ((1 - τ) * t0 + τ * t1)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp



noncomputable def fiberTransport {t0 : I} (m : matSlice γ Γ t0) (t1 : I) : MatSpace γ Γ :=
  let p := m.1.out.center.1
  let a : SidesAt (𝒮 (ℱ F) S) (p, t0) := ⟨m.1.out, Prod.mk_inj.mpr ⟨rfl, m.2⟩⟩

  let R : Rollercoaster (𝒪 γ Γ) (p, t0) (p, t1) := Rollercoaster.exists_of_path
    (·.2.1) (𝒪_cover γ Γ hγ realizer_basis) ((Path.refl p).prod (segment t0 t1)) |>.choose

  let Ca0 : Chariot (𝒢 γ Γ) (p, t0) := ⟨(𝒢 γ Γ a ·), ((𝒢 γ Γ).trans a · ·)⟩
  let Ca1 : Chariot (𝒢 γ Γ) (p, t1) := R.jumpAll (chariot_transfer' γ Γ sidesAt_nonempty) Ca0

  have h0 : Ca0.allSymmetric := (Subgroup.mem_closure_of_mem ⟨(p, t0), a, ·, rfl⟩)
  have h1 : Ca1.allSymmetric := R.jumpAll_induction (chariot_transfer' γ Γ sidesAt_nonempty)
    h0 (chariot_allSymmetric_transfer' γ Γ sidesAt_nonempty)

  Ca1.toMatSpace h1




theorem fiberTransport_mem_slice {t0 : I} (m : matSlice γ Γ t0) (t1 : I) :
  fiberTransport γ Γ hγ realizer_basis sidesAt_nonempty m t1 ∈ matSlice γ Γ t1 := by

  unfold matSlice --Quotient.out Quot.out
  simp?

  let p := m.1.out.center.1

  if h : (p, t1) ∈ 𝒰 (ℱ F) then
    /-rw [dif_pos h]
    rw [Sides.center_transport' _ _ (sidesAt_nonempty _ |>.some.2 ▸ h)]
    --rw [Sides.restrict_comm _ _]
    --rw [transport_eq_transportOf]
    --simp only
    --unfold transportOf


    -- we need transport to preserve the t=1. this is a property of our extruded F
    -/
    sorry
  else
    unfold fiberTransport Chariot.toMatSpace Chariot.toMatSpace_apply
    simp only
    exact sorry --dif_neg h ▸ congr_arg Prod.snd (sidesAt_nonempty (p, t1)).some.2





-- this one has the ending-time data and takes t0 explicitly
noncomputable def fiberTransport' (t0 t1 : I) (m : matSlice γ Γ t0) : matSlice γ Γ t1 :=
  ⟨fiberTransport γ Γ hγ realizer_basis sidesAt_nonempty m t1,
    fiberTransport_mem_slice γ Γ hγ realizer_basis sidesAt_nonempty m t1⟩







theorem fiberTransport'_symm_leftInv (t0 t1 : I) :
  Function.LeftInverse
    (fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t1 t0)
    (fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t0 t1) := by
  intro ⟨m', hx⟩
  induction m' using Quotient.inductionOn with | _ x => _
  apply Subtype.eq
  apply Quotient.sound
  split
  · right
    -- use rel_of_homotopic
    sorry
  · left
    -- because theres only one side on that point
    sorry



theorem continuous_fiberTransport' (t0 t1 : I) :
  Continuous (fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t0 t1) := by
  -- this will be hard
  sorry




private noncomputable def surface_independence_helper (t0 t1 : I) :
    matSlice γ Γ t0 ≃ₜ matSlice γ Γ t1 where
  toFun := fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t0 t1
  invFun := fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t1 t0
  left_inv := fiberTransport'_symm_leftInv γ Γ hγ realizer_basis sidesAt_nonempty t0 t1
  right_inv := fiberTransport'_symm_leftInv γ Γ hγ realizer_basis sidesAt_nonempty t1 t0
  continuous_toFun := continuous_fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t0 t1
  continuous_invFun := continuous_fiberTransport' γ Γ hγ realizer_basis sidesAt_nonempty t1 t0


noncomputable def surface_independence
  (h0 : Function.Bijective (to_sideSlice F S 0))
  (h1 : Function.Bijective (to_sideSlice F S 1)) :
    MatSpaceₜ γ Γ 0 ≃ₜ MatSpaceₜ γ Γ 1 :=
  (to_matSlice_homeomorph γ Γ h0).trans <|
  (surface_independence_helper γ Γ hγ realizer_basis sidesAt_nonempty 0 1).trans
  (to_matSlice_homeomorph γ Γ h1).symm



#check surface_independence

end Portal
