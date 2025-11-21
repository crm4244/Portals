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


variable {X : TopCat}


/-- Total space of stalks of a sheaf of types. -/
def Total (F : X.Sheaf (Type)) := Σ x : X, Presheaf.stalk F.val x


/-- Projection to the base space. -/
def proj {F : X.Sheaf (Type)} (p : Total F) : X := p.1


/-- Basic opens: germs of a section over an open. -/
def basicOpen {F : X.Sheaf (Type)} (U : Opens X) (s : F.val.obj (op U)) : Set (Total F) :=
  { p | ∃ hp : p.1 ∈ U, p.2 = Presheaf.germ F.val U p.1 hp s }


/-- The generating set of basic opens. -/
def basicOpens (F : X.Sheaf (Type)) : Set (Set (Total F)) :=
  { S | ∃ (U : Opens X) (s : F.val.obj (op U)), S = basicOpen U s }


/-- Topology on the total space. -/
instance topology (F : X.Sheaf (Type)) : TopologicalSpace (Total F) :=
  generateFrom (basicOpens F)


/-- The étale space as a topological space. -/
def space (F : X.Sheaf (Type)) : TopCat :=
  let : TopologicalSpace (Total F) := topology F
  TopCat.of (Total F)


theorem proj_continuous (F : X.Sheaf (Type)) : @Continuous (Total F) X (topology F) X.str proj :=
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


def projMap {F : X.Sheaf (Type)} : space F ⟶ X :=
  TopCat.ofHom ⟨proj, proj_continuous F⟩

/-- Local homeomorphism structure on the projection. -/
def projIsLocalHomeomorph {F : X.Sheaf (Type)} :
    IsLocalHomeomorph (proj : Total F → X) :=
  by
    intro ⟨x, ξ⟩
    -- OpenPartialHomeomorph.mk
    #check Presheaf.germ_exist F.val x ξ

    -- build charts using basicOpen U s
    -- show source = basicOpen U s
    -- show target = U
    -- define local inverse x ↦ ⟨x, germ⟩
    -- sheaf condition used for compatibility
    sorry

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
