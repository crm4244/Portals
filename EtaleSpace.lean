import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order


open CategoryTheory Opposite Topology TopologicalSpace
attribute [local instance] Types.instFunLike Types.instConcreteCategory

namespace TopCat
namespace Sheaf
namespace EtaleSpace

universe u
variable {X : TopCat}


/-- Total space of stalks of a sheaf of Type us. -/
def Total (F : X.Sheaf (Type u)) := Σ x : X, Presheaf.stalk F.val x


/-- Projection to the base space. -/
def proj {F : X.Sheaf (Type u)} (p : Total F) : X := p.1


/-- Basic opens: germs of a section over an open. -/
def basicOpen {F : X.Sheaf (Type u)} (U : Opens X) (s : F.val.obj (op U)) : Set (Total F) :=
  { p | ∃ hp : p.1 ∈ U, p.2 = Presheaf.germ F.val U p.1 hp s }


/-- The generating set of basic opens. -/
def basicOpens (F : X.Sheaf (Type u)) : Set (Set (Total F)) :=
  { S | ∃ (U : Opens X) (s : F.val.obj (op U)), S = basicOpen U s }


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
        match TopCat.Presheaf.germ_exist F.val x ξ with
        | ⟨U, hxU, s, hξ⟩ =>
          let morph := Opens.infLELeft U Vo
          let s' := F.val.map morph.op s
          let O := basicOpen (U ⊓ Vo) s'
          have hO1 : O ∈ basicOpens F := Set.mem_setOf_eq ▸ ⟨(U ⊓ Vo), s', rfl⟩
          have hO2 : proj '' (Subtype.mk O hO1).1 ⊆ V :=
            Set.image_subset_iff.mpr fun _ hq ↦ Set.mem_preimage.mpr hq.1.2
          have hxUVo : x ∈ U ⊓ Vo := Opens.mem_inf.mpr ⟨hxU, Set.mem_preimage.mp hp⟩

          ⟨⟨⟨O, hO1⟩, hO2⟩, hxUVo, hξ ▸ Presheaf.germ_res F.val morph x hxUVo ▸ by rfl⟩))

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
    match Presheaf.germ_exist F.val x ξ with
    | ⟨U, hxU, s, h_germ_concrete⟩ =>
      let W := basicOpen U s
      let inv_on_U (y : U) : Total F := ⟨y.1, Presheaf.germ F.val U y.1 y.2 s⟩

      let f : OpenPartialHomeomorph (Total F) X := {
        toFun := proj
        invFun := fun y ↦ if h : y ∈ U then inv_on_U ⟨y, h⟩ else inv_on_U ⟨x, hxU⟩
        source := W
        target := proj '' W
        map_source' := fun p hp ↦ ⟨p, hp, rfl⟩
        map_target' := fun y ⟨p, ⟨hpU, _⟩, (hpy : p.1 = y)⟩ ↦
          dif_pos (hpy ▸ hpU) ▸ Set.mem_setOf_eq ▸ ⟨(hpy ▸ hpU), rfl⟩

        left_inv' := fun ⟨y, μ⟩ ⟨(hpU : proj ⟨y, μ⟩ ∈ U), (h_germ : μ = _)⟩ ↦
          dif_pos hpU ▸ h_germ ▸ rfl

        right_inv' := fun y ⟨p, ⟨hpU, _⟩, (hpy : p.1 = y)⟩ ↦ dif_pos (hpy ▸ hpU) ▸ rfl
        open_source := isOpen_generateFrom_of_mem (Set.mem_setOf_eq ▸ ⟨U, s, rfl⟩)
        open_target := (
          Set.Subset.antisymm
            (fun y (⟨_, ⟨hmem, _⟩, heq⟩ : y ∈ proj '' W) ↦ heq ▸ hmem)
            (fun y hyU ↦ (Set.mem_image proj W y).mpr
              ⟨⟨y, Presheaf.germ F.val U y hyU s⟩, ⟨Set.mem_setOf_eq ▸ ⟨hyU, rfl⟩, rfl⟩⟩)
            : proj '' W = U.1
          ) ▸ U.2

        continuousOn_toFun := continuousOn_iff_continuous_restrict.mpr
          (Continuous.comp (proj_continuous F) continuous_subtype_val)

        continuousOn_invFun := by
          apply continuousOn_iff.mpr
          rintro _ ⟨⟨y, μ⟩, ⟨(hpU), (h_germ : μ = _)⟩, rfl⟩ V hV_open hyV
          use proj '' V
          split_ands
          ·
            sorry
          · apply (Set.mem_image proj V _).mpr
            exact ⟨⟨y, μ⟩, by
              rw [h_germ]
              have h := dif_pos hpU ▸ hyV
              exact h

              , rfl⟩



          · rintro _ ⟨⟨⟨a, b⟩, hvV, rfl⟩, w, ⟨(hwU : proj _ ∈ _), hw_germ⟩, hwv⟩
            apply Set.mem_preimage.mpr
            rw [dif_pos (hwv ▸ hwU)]
            unfold inv_on_U proj
            simp

            sorry

          --rw [dif_pos] at hifV
          --unfold inv_on_U proj at hifV
          --simp at hifV
      }

      exact ⟨f, Set.mem_setOf_eq ▸ ⟨hxU, h_germ_concrete ▸ rfl⟩, rfl⟩



def projIsOpenMap {F : X.Sheaf (Type u)} :
    IsOpenMap (projMap : space F ⟶ X) :=
  by
    sorry

/-- The projection is an étale map. -/
def isEtale {X : TopCat} {F : X.Sheaf (Type u)} :
    IsOpenMap (projMap : space F ⟶ X) ∧ IsLocalHomeomorph (projMap : space F ⟶ X) :=
  ⟨projIsOpenMap, projIsLocalHomeomorph⟩


end EtaleSpace
end Sheaf
end TopCat
