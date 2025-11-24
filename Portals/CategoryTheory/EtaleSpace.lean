import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order


namespace TopCat
namespace Sheaf
namespace EtaleSpace


open CategoryTheory Opposite Presheaf Topology TopologicalSpace
attribute [local instance] Types.instFunLike Types.instConcreteCategory


universe u
variable {X : TopCat}


/-- Total space of stalks of a sheaf of Type us. -/
def Total (F : X.Sheaf (Type u)) := Σ x : X, stalk F.val x


/-- Projection to the base space. -/
def proj {F : X.Sheaf (Type u)} : Total F → X := Sigma.fst


/-- Basic opens: germs of a section over an open. -/
def basicOpen {F : X.Sheaf (Type u)} (U : Opens X) (s : F.val.obj (op U)) : Set (Total F) :=
  { p | ∃ hp : p.1 ∈ U, p.2 = germ F.val U p.1 hp s }


/-- The generating set of basic opens. -/
def basicOpens (F : X.Sheaf (Type u)) : Set (Set (Total F)) :=
  { basicOpen U s | (U : Opens X) (s : F.val.obj (op U)) }


/-- Topology on the total space. -/
instance topology (F : X.Sheaf (Type u)) : TopologicalSpace (Total F) :=
  generateFrom (basicOpens F)


/-- The étale space as a topological space. -/
def space (F : X.Sheaf (Type u)) : TopCat :=
  let : TopologicalSpace (Total F) := topology F
  TopCat.of (Total F)


theorem proj_continuous (F : X.Sheaf (Type u)) : @Continuous (Total F) X (topology F) X.str proj :=
  Continuous.mk fun V hV ↦
  let Vo := Opens.mk V hV

  have h : proj ⁻¹' V = ⋃ U : { U : basicOpens F // proj '' U.1 ⊆ V }, U.1.1 := by
    apply Set.Subset.antisymm
      (fun ⟨x, ξ⟩ hp ↦ Set.mem_iUnion.mpr (
        match germ_exist F.val x ξ with
        | ⟨U, hxU, s, hξ⟩ =>
          let morph := Opens.infLELeft U Vo
          let s' := F.val.map morph.op s
          let O := basicOpen (U ⊓ Vo) s'
          have hO1 : O ∈ basicOpens F := Set.mem_setOf_eq ▸ ⟨(U ⊓ Vo), s', rfl⟩
          have hO2 : proj '' (Subtype.mk O hO1).1 ⊆ V :=
            Set.image_subset_iff.mpr fun _ hq ↦ Set.mem_preimage.mpr hq.1.2
          have hxUVo : x ∈ U ⊓ Vo := Opens.mem_inf.mpr ⟨hxU, Set.mem_preimage.mp hp⟩

          ⟨⟨⟨O, hO1⟩, hO2⟩, hxUVo, hξ ▸ germ_res F.val morph x hxUVo ▸ by rfl⟩))

    · exact fun T ⟨U'', ⟨U, (hU : ↑↑U = U'')⟩, hT⟩ ↦
        Set.mem_preimage.mpr (U.2 ((Set.mem_image proj U.1.1 (proj T)).mpr ⟨T, ⟨hU ▸ hT, rfl⟩⟩))

  h ▸ isOpen_iUnion fun U ↦ isOpen_generateFrom_of_mem U.1.2


def projMap {F : X.Sheaf (Type u)} : space F ⟶ X :=
  TopCat.ofHom ⟨proj, proj_continuous F⟩


open Classical in

/-- Local homeomorphism structure on the projection. -/
def projIsLocalHomeomorph {F : X.Sheaf (Type u)} :
    IsLocalHomeomorph (proj : Total F → X) :=
  by
    intro ⟨x, ξ⟩
    match germ_exist F.val x ξ with
    | ⟨U, hxU, s, h_germ_concrete⟩ =>
      let W := basicOpen U s
      let inv_on_U (u : U) : Total F := ⟨u.1, germ F.val U u.1 u.2 s⟩
      let UorIgnore y : U := if hyU : y ∈ U then ⟨y, hyU⟩ else ⟨x, hxU⟩
      let invFun y := inv_on_U (UorIgnore y)
      have UorIgnore_of_mem (u : U) : UorIgnore u.1 = u := dif_pos u.2


      let f : OpenPartialHomeomorph (Total F) X := {
        toFun := proj
        invFun := invFun
        source := W
        target := proj '' W
        map_source' := fun p hp ↦ ⟨p, hp, rfl⟩
        map_target' := fun _ _ ↦ Set.mem_setOf_eq ▸ ⟨SetLike.coe_mem _, rfl⟩
        left_inv' := fun p ⟨hpU, h_germ⟩ ↦ by
          unfold invFun inv_on_U
          exact UorIgnore_of_mem ⟨p.1, hpU⟩ ▸ h_germ ▸ rfl

        right_inv' := fun y ⟨p, ⟨hpU, _⟩, (hpy : p.1 = y)⟩ ↦ by
          unfold invFun inv_on_U
          exact UorIgnore_of_mem ⟨y, hpy ▸ hpU⟩ ▸ rfl

        open_source := isOpen_generateFrom_of_mem (Set.mem_setOf_eq ▸ ⟨U, s, rfl⟩)
        open_target := (
          Set.Subset.antisymm
            (fun y (⟨_, ⟨hmem, _⟩, heq⟩ : y ∈ proj '' W) ↦ heq ▸ hmem)
            (fun y hyU ↦ (Set.mem_image proj W y).mpr
              ⟨⟨y, germ F.val U y hyU s⟩, ⟨Set.mem_setOf_eq ▸ ⟨hyU, rfl⟩, rfl⟩⟩)
            : proj '' W = U.1
          ) ▸ U.2

        continuousOn_toFun := continuousOn_iff_continuous_restrict.mpr
          (Continuous.comp (proj_continuous F) continuous_subtype_val)

        continuousOn_invFun := by
          unfold proj invFun inv_on_U
          apply continuousOn_iff_continuous_restrict.mpr
          apply continuous_generateFrom_iff.mpr
          rintro _ ⟨V, t, rfl⟩
          apply isOpen_induced_iff.mpr
          use V
          split_ands
          · exact V.2
          · apply Set.Subset.antisymm
            · rintro ⟨_, ⟨y, μ⟩, ⟨hyU : y ∈ U,
                hp_germ⟩, rfl⟩ _hyV
              have hyV : y ∈ V := Set.mem_preimage.mp _hyV
              apply Set.mem_preimage.mpr
              unfold basicOpen
              rw [Set.restrict_apply]
              rw [UorIgnore_of_mem ⟨y, hyU⟩]
              rw [Set.mem_setOf_eq]
              use hyV

              simp only
              let __ : (Subtype.mk y hyU).2 = hyU := rfl
              rw [__]

              rw [← germ_res F.val (Opens.infLELeft U V) y ⟨hyU, hyV⟩]
              rw [← germ_res F.val (Opens.infLERight U V) y ⟨hyU, hyV⟩]

              simp
              apply congrArg

              sorry

            · rintro ⟨_, ⟨y, μ⟩, ⟨hyU : y ∈ U,
                hp_germ : μ = germ F.val U y hyU s⟩, rfl⟩ ⟨h, _⟩
              apply Set.mem_preimage.mpr
              simp only [Set.restrict_apply] at ⊢ h
              have h := SetLike.mem_coe.mpr (UorIgnore_of_mem ⟨y, hyU⟩ ▸ h)
              exact h
      }

      exact ⟨f, Set.mem_setOf_eq ▸ ⟨hxU, h_germ_concrete ▸ rfl⟩, rfl⟩



def projIsOpenMap {F : X.Sheaf (Type u)} :
    IsOpenMap (projMap : space F ⟶ X) := by
  #check isSheaf_iff_isSheafPairwiseIntersections
  sorry

/-- The projection is an étale map. -/
def isEtale {X : TopCat} {F : X.Sheaf (Type u)} :
    IsOpenMap (projMap : space F ⟶ X) ∧ IsLocalHomeomorph (projMap : space F ⟶ X) :=
  ⟨projIsOpenMap, projIsLocalHomeomorph⟩


end EtaleSpace
end Sheaf
end TopCat
