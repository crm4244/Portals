import PortalTheory.MaterialSpace
import PortalTheory.Chariot
import PortalTheory.RealizerRollercoaster
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


theorem continuous_proj {t : Y} : Continuous (@proj X _ t) :=
  continuous_fst.comp continuous_subtype_val

theorem continuous_incl (t : Y) : Continuous (@incl X _ t) :=
  Continuous.prodMk_left t |>.subtype_mk _


def homeomorph {t : Y} : Slice X t ≃ₜ X where
  toFun := proj
  invFun := incl t
  left_inv := incl_proj
  right_inv := proj_incl
  continuous_toFun := continuous_proj
  continuous_invFun := continuous_incl t



open Topology

theorem isEmbedding_proj {t : Y} : IsEmbedding (@proj X _ t) :=
  homeomorph.isEmbedding


theorem isEmbedding_incl (t : Y) : IsEmbedding (@incl X _ t) :=
  homeomorph.symm.isEmbedding


def incl' (t : Y) : X → X × Y := Subtype.val ∘ (@incl X _ t)


theorem isEmbedding_incl' (t : Y) : IsEmbedding (@incl' X _ t) :=
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
variable (Γ : GeneralizedMultiset (Equiv.Perm (ℱ F)) → (Equiv.Perm (ℱ F)))
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

noncomputable abbrev Γₜ (Γ : GeneralizedMultiset (Equiv.Perm (ℱ F)) → (Equiv.Perm (ℱ F))) :
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


def 𝒪 : Set (Set (X × I)) :=
  {U | ∃ (hU : IsOpen U) (p : X × I) (R : ComponentRealizer ⟨U, hU⟩ (𝒮 (ℱ F) S) p),
    (𝒢 γ Γ).respects_realizer R}


def matSlice (t : I) := {m : MatSpace γ Γ | ∃ x, m = ⟦x⟧ ∧ x.center.2 = t}



def bijProjT (F : Set (PortalMap X Y)) (S : Set (Y × I)) (t : I) : Prop :=
  Function.Bijective <| Sides.map (S := 𝒮 F (Sₜ t S)) (Y := @Slice X I t) Slice.isEmbedding_proj


def matSpaceHomeomorphT {t : I} (h_bijective : bijProjT F S t) :
    MatSpaceₜ γ Γ t ≃ₜ matSlice γ Γ t where
  toFun m := by
    #check Classical.choose m.exists_rep
    #check Equiv.ofBijective _ h_bijective |>.invFun
    sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry




section fiberTransport

variable [h_nonempty : ∀ p, Nonempty (SidesAt (𝒮 (ℱ F) S) p)]



-- reformatting some functions from Chariot.lean to fit with what Rollercoaster expects

private noncomputable def chariot_transfer'
  {U : 𝒪 γ Γ} (p q : U.1) (C : Chariot (𝒢 γ Γ) p) :
    Chariot (𝒢 γ Γ) q :=
  C.transfer U.2.2.choose_spec.2 p.2 q.2

private def chariot_allSymmetric_transfer'
  {U : 𝒪 γ Γ} {p q : U.1} (C : Chariot (𝒢 γ Γ) p)
  (hC : C.allSymmetric) :
    (chariot_transfer' γ Γ p q C).allSymmetric :=
  C.allSymmetric_transfer hC U.2.2.choose_spec.2 p.2 q.2




noncomputable def fiberTransport {a : Sides (𝒮 (ℱ F) S)}
  (R : Rollercoaster (𝒪 γ Γ) a.center (a.center.1, 1)) :
    matSlice γ Γ 1 :=

  let Ca0 : Chariot (𝒢 γ Γ) a.center := ⟨(𝒢 γ Γ ⟨a, rfl⟩ ·), ((𝒢 γ Γ).trans ⟨a, rfl⟩ · ·)⟩
  let Ca1 : Chariot (𝒢 γ Γ) (a.center.1, 1) := R.jumpAll (chariot_transfer' γ Γ) Ca0

  have h0 : Ca0.allSymmetric := fun _ ↦ Subgroup.mem_closure_of_mem ⟨_, _, _, rfl⟩
  have h1 : Ca1.allSymmetric := R.jumpAll_induction
    (chariot_transfer' γ Γ) h0 (chariot_allSymmetric_transfer' γ Γ)

  ⟨Ca1.toMatSpace h1, ⟨_, rfl, by
    split
    · -- we need transport to preserve the t=1. this is a property of our extruded F
      sorry
    · exact congr_arg Prod.snd (h_nonempty (a.center.1, 1)).some.2⟩⟩


-- this one is independent of the choice of Rollercoaster
noncomputable def fiberTransport' (a : Sides (𝒮 (ℱ F) S)) :=
  Quotient.lift
    (s := Rollercoaster.instSetoidRel (chariot_transfer' γ Γ))
    (fiberTransport γ Γ (a := a))
    (fun _ _ _ ↦ Subtype.mk_eq_mk.mpr <| Quotient.eq.mpr <| Or.inl rfl)


-- this one is independent of the choice of representative side a
noncomputable def fiberTransport'' : MatSpace γ Γ → matSlice γ Γ 1 :=
  Quotient.lift (s := matSpaceSetoid γ Γ)
    (fun a ↦ fiberTransport' γ Γ a (
      -- choose the rollercoaster following the fiber path using Rollercoaster.exists_follows
      sorry))
    (fun a b h ↦ by
      --
      sorry)


-- this one includes initial slice data, and then ignores it
noncomputable def fiberTransport''' : matSlice γ Γ 0 → matSlice γ Γ 1 :=
  fun ⟨m, _⟩ ↦ fiberTransport'' γ Γ m



theorem continuous_fiberTransport''' (hγ : (𝒢 γ Γ).isLocallyConsistent) :
  Continuous (fiberTransport''' γ Γ) := sorry


end fiberTransport






private noncomputable def surface_independence_helper
  (hγ : (𝒢 γ Γ).isLocallyConsistent)
  (h_nonempty : ∀ p, Nonempty (SidesAt (𝒮 (ℱ F) S) p)) :
    matSlice γ Γ 0 ≃ₜ matSlice γ Γ 1 where
  toFun := fiberTransport''' γ Γ
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  continuous_toFun := continuous_fiberTransport''' γ Γ hγ
  continuous_invFun := sorry



noncomputable def surface_independence (hγ : (𝒢 γ Γ).isLocallyConsistent)
  (h_nonempty : ∀ p, Nonempty (SidesAt (𝒮 (ℱ F) S) p))
  (h0 : bijProjT F S 0) (h1 : bijProjT F S 1) :
    MatSpaceₜ γ Γ 0 ≃ₜ MatSpaceₜ γ Γ 1 :=
  (matSpaceHomeomorphT γ Γ h0).trans <|
  (surface_independence_helper γ Γ hγ h_nonempty).trans
  (matSpaceHomeomorphT γ Γ h1).symm



#check surface_independence

end Portal
