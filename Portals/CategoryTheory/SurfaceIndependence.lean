import Portals.CategoryTheory.MaterialSpace
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

theorem isEmbedding_incl (t : Y) : IsEmbedding (incl (X := X) t) :=
  homeomorph.symm.isEmbedding


def incl' (t : Y) : X → X × Y := Subtype.val ∘ (incl (X := X) t)


theorem isEmbedding_incl' (t : Y) : IsEmbedding (incl' (X := X) t) :=
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


def 𝒪 (p : X) : Set (Opens (X × I)) :=
  {U | ∃ (t : I) (R : ComponentRealizer U (𝒮 (ℱ F) S) (p, t)),
    (combinedGluingPattern 𝒢_trans).respects_realizer R}

abbrev fiber (p : X) := {(x, _) : X × I | x = p}

theorem 𝒪_covers_fiber (p : X) : fiber p ⊆ ⋃ (U : 𝒪 𝒢_trans p), U := by
  -- follows from local consistency
  sorry

theorem exists_finite_subcover_𝒪_of_fiber (p : X) :
  ∃ t : Finset (𝒪 𝒢_trans p), Set.univ ⊆ ⋃ i ∈ t, Prod.mk p ⁻¹' i.1.1 :=
  (compactSpace_Icc 0 1 : CompactSpace I).isCompact_univ.elim_finite_subcover
    (fun U : 𝒪 𝒢_trans p ↦ Prod.mk p ⁻¹' U)
    (fun ⟨⟨_, U⟩, _⟩ ↦ Continuous.prodMk_right (Y := I) p |>.isOpen_preimage _ U)
    (fun _ _ ↦ let ⟨_, ⟨U, rfl⟩, h⟩ := 𝒪_covers_fiber 𝒢_trans p rfl; ⟨_, ⟨U, rfl⟩, h⟩)

#check Quotient

def 𝒯 (hγ : (combinedGluingPattern 𝒢_trans).isLocallyConsistent) (a : Sides (𝒮 F (Sₜ 0 S)))
  (t : I) (α : Sides.at_point (𝒮 (ℱ F) S) (a.center, t)) : Equiv.Perm F := by


    -- for each finite subcover, show inductively that the product is well defined
    -- build a setoid out of the finite subcovers related by matching outputs

    sorry

structure rollercoaster (p : X) where
  list_of_ts : List I
  list_of_Us : List (𝒪 𝒢_trans p)
  h_length : list_of_ts.length = list_of_Us.length + 1
  t_mem : ∀ n : Fin list_of_Us.length, (p, list_of_ts[n]) ∈ list_of_Us[n].1
  t_next_mem : ∀ n : Fin list_of_Us.length, (p, list_of_ts[n.succ]) ∈ list_of_Us[n].1



def surface_independence (hγ : (combinedGluingPattern 𝒢_trans).isLocallyConsistent)
  (h0 : Function.Bijective (Sides.map (S := S) (Y := @Slice Y I 0) IsEmbedding.subtypeVal))
  (h1 : Function.Bijective (Sides.map (S := S) (Y := @Slice Y I 1) IsEmbedding.subtypeVal)) :
    MatSpaceₜ 𝒢_trans transport_symmetry 0 ≃ₜ MatSpaceₜ 𝒢_trans transport_symmetry 1 := by

  sorry


#check surface_independence

end Portal
