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


end Slice



variable {X : Type*} [TopologicalSpace X] {Y : Type*} [TopologicalSpace Y]



section extrude
variable (Z : Type*) [TopologicalSpace Z]

open Topology in private def extrude : PortalMap Y X → PortalMap (Y × Z) (X × Z)
  | f => ⟨(·.map f id), f.2.prodMap IsOpenEmbedding.id⟩

private theorem extrude_injective [Nonempty Z] : Function.Injective (extrude (X := X) (Y := Y) Z) :=
  fun _ _ h ↦ Subtype.eq <| funext fun y ↦ And.left <| Prod.eq_iff_fst_eq_snd_eq.mp <|
    (congr_fun <| Subtype.mk_eq_mk.mp h) (y, Classical.choice ‹Nonempty Z›)


-- use OfLeftInverse?
private noncomputable def extrude_equiv [Nonempty Z] (F : Set (PortalMap Y X)) :
  F ≃ Set.range (fun f : F ↦ extrude Z f.1) :=
    Equiv.ofInjective _ <| Subtype.restrict_injective (· ∈ F) <| extrude_injective Z


end extrude



abbrev ℱ (F : Set (PortalMap Y X)) := Set.range (fun f : F ↦ extrude I f.1)
variable {F : Set (PortalMap Y X)}

variable {S : Set (Y × I)}
variable {γ : GluingPattern S (Equiv.Perm (ℱ F))}
variable {Γ : GeneralizedMultiset (Equiv.Perm (ℱ F)) → (Equiv.Perm (ℱ F))}
variable {𝒢_trans : ∀ {p : X × I} (a b c : Sides.at_point (𝒮 (ℱ F) S) p),
  Γ (quattle γ a b) * Γ (quattle γ b c) = Γ (quattle γ a c)}
variable {transport_symmetry : ∀ P (f g : ℱ F) (q : X × I)
  (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
    transportOf P ⟨q, hf⟩ = transportOf P ⟨q, hg⟩}

#check MatSpace γ Γ 𝒢_trans transport_symmetry


--X₀ := Slice X (0 : I)
--Y₀ := Slice Y (0 : I)
-- F := F
abbrev S₀ (S : Set (Y × I)) : Set Y := @Slice.proj Y I 0 '' ((↑) ⁻¹' S)

abbrev γ₀ (γ : GluingPattern S (Equiv.Perm (ℱ F))) :
  GluingPattern (S₀ S) (Equiv.Perm F) := sorry

noncomputable abbrev Γ₀ (Γ : GeneralizedMultiset (Equiv.Perm (ℱ F)) → (Equiv.Perm (ℱ F))) :
  GeneralizedMultiset (Equiv.Perm F) → (Equiv.Perm F) :=
    fun 𝒰 ↦ (extrude_equiv I F).symm.permCongr <| Γ <| 𝒰.map
      (fun G ↦ ⟨G.index, fun i ↦ (extrude_equiv I F).permCongr (G.val i)⟩)
      (fun _ ⟨_, _⟩ ⟨h1, h2⟩ ↦ ⟨h1, funext fun i ↦
        congr_arg (extrude_equiv I F).permCongr (congr_fun h2 i)⟩)

include 𝒢_trans in theorem 𝒢₀_trans : ∀ {p : X} (a b c : Sides.at_point (𝒮 F (S₀ S)) p),
  Γ₀ Γ (quattle (γ₀ γ) a b) * Γ₀ Γ (quattle (γ₀ γ) b c) = Γ₀ Γ (quattle (γ₀ γ) a c) := by

  intro p a b c

  --unfold HMul.hMul instHMul Mul.mul Equiv.Perm.instMul Equiv.trans
  --simp only
  apply Equiv.ext
  intro f
  simp only [Equiv.Perm.coe_mul]
  unfold Γ₀
  simp only [Function.comp_apply, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    EmbeddingLike.apply_eq_iff_eq]

  unfold quattle GeneralizedMultiset.of_function GenMulti.of_function
  simp only [Quotient.map_mk]

  let a' : Sides.at_point (𝒮 (ℱ F) S) (p, 0) := sorry
  let b' : Sides.at_point (𝒮 (ℱ F) S) (p, 0) := sorry
  let c' : Sides.at_point (𝒮 (ℱ F) S) (p, 0) := sorry
  have h := (𝒢_trans (p := (p, 0)) a' b' c')

  unfold quattle GeneralizedMultiset.of_function GenMulti.of_function at h


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
          val := fun i ↦ (extrude_equiv I F).permCongr (recommendation_map (γ₀ γ) (f := i.1) _ _) }
      { index := relevant_portal_maps (ℱ F) (p, 0),
          val := fun i ↦ recommendation_map (f := i.1) γ _ _ })



  sorry

include transport_symmetry in theorem transport_symmetry₀ : ∀ P (f g : F) (q : X)
  (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
    transportOf P ⟨q, hf⟩ = transportOf P ⟨q, hg⟩ := by
  intro P f g q hf hg

  let f' := extrude_equiv I F f
  let g' := extrude_equiv I F g
  let P' := (extrude_equiv I F).permCongr P

  have h_prod_mem {l : F} (hl : q ∈ l.1.range) : (q, 0) ∈ (extrude_equiv I F l).1.range :=
    ⟨(l.1.inv_range ⟨q, hl⟩, 0), Prod.map_apply _ _ _ _ |>.trans <|
      Prod.eq_iff_fst_eq_snd_eq.mpr ⟨l.1.inv_right ⟨q, hl⟩, rfl⟩⟩

  have h := transport_symmetry P' f' g' (q, 0) (h_prod_mem hf) (h_prod_mem hg)

  unfold transportOf at h ⊢
  unfold P' f' g' at h
  unfold extrude_equiv at h
  simp only [Equiv.ofInjective_apply, Equiv.permCongr_apply, Equiv.ofInjective_symm_apply] at h
  unfold extrude Prod.map at h
  simp only [Prod.mk.injEq] at h
  apply And.left at h

  have h_final {l : F} (hl : q ∈ l.1.range) :
    ((extrude I l.1).inv_range ⟨(q, 0), h_prod_mem hl⟩).1 = l.1.inv_range ⟨q, hl⟩ :=
      l.1.2.injective <| Eq.trans
        (by simpa only using congr_arg Prod.fst <| extrude_equiv I F l |>.1.inv_right _)
        (l.1.inv_right ⟨q, hl⟩).symm

  exact (h_final hf) ▸ (h_final hg) ▸ h


end Portal
