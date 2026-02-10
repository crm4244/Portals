import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order


namespace TopCat
namespace Sheaf


open CategoryTheory Opposite Presheaf Topology TopologicalSpace

universe v u
variable {X : TopCat.{v}} {C : Type u} [Category.{v} C] [Limits.HasColimits C]
variable {FC : C → C → Type*} {CC : C → Type v} [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory.{v} C FC] [Limits.PreservesFilteredColimits (CategoryTheory.forget C)]


def EtaleSpace (ℱ : X.Presheaf C) : Type v :=
  Σ p : X, (CategoryTheory.forget C).obj (stalk ℱ p)



namespace EtaleSpace
variable {ℱ : X.Presheaf C}


def proj : EtaleSpace ℱ → X := Sigma.fst


def basicSet (U : Opens X) (s : (CategoryTheory.forget C).obj (ℱ.obj (op U))) :
    Set (EtaleSpace ℱ) :=
  { p | ∃ hp : p.1 ∈ U, p.2 = germ ℱ U p.1 hp s }


variable (ℱ)




def basis : Set (Set (EtaleSpace ℱ)) :=
  { basicSet U s | (U : Opens X) (s : (CategoryTheory.forget C).obj (ℱ.obj (op U))) }


instance topology : TopologicalSpace (EtaleSpace ℱ) :=
  generateFrom (basis ℱ)


def obj : TopCat := @TopCat.of (EtaleSpace ℱ) (topology ℱ)


instance basis_isBasis : IsTopologicalBasis (basis ℱ) :=
  {
    exists_subset_inter := fun _ ⟨_, sU, hU⟩ _ ⟨_, sV, hV⟩ ⟨p, _⟩ ⟨mU, mV⟩ ↦
      have ⟨W, hpW, hWU, hWV, hW⟩ := ℱ.germ_eq p (hU ▸ mU).1 (hV ▸ mV).1 sU sV
        ((hU ▸ mU).2.symm.trans (hV ▸ mV).2)
      ⟨basicSet W ((ConcreteCategory.hom (ℱ.map hWU.op)) sU),
        ⟨W, _, rfl⟩,
        ⟨hpW, (hU ▸ mU).2.trans
          (by rw [(ℱ.germ_res hWU p hpW).symm]; apply ConcreteCategory.comp_apply)⟩,
        fun ⟨q, _⟩ ⟨m, h⟩ ↦
          ⟨ -- we could make a function to cover the two cases because they are similar
          hU ▸ ⟨hWU.le m, h.trans
            (by rw [← ℱ.germ_res hWU q m, ConcreteCategory.comp_apply])⟩,
          hV ▸ ⟨hWV.le m, h.trans <| (congr_arg (ℱ.germ W q m) hW).trans
            (by rw [← ℱ.germ_res hWV q m, ConcreteCategory.comp_apply]; rfl)⟩⟩⟩
    sUnion_eq := Set.eq_univ_of_forall fun ⟨p, ξ⟩ ↦
      have ⟨U, hpU, s, h⟩ := ℱ.germ_exist p ξ
      Set.mem_sUnion.mpr  ⟨basicSet U s, ⟨U, s, rfl⟩, hpU, h.symm⟩
    eq_generateFrom := rfl
  }


variable {ℱ}

theorem proj_continuous :
    @Continuous (EtaleSpace ℱ) X (topology ℱ) X.str proj :=
  Continuous.mk fun V hV ↦
  let Vo : Opens X := ⟨V, hV⟩
  have h : proj ⁻¹' V = ⋃ U : { U : basis ℱ // proj '' U.1 ⊆ V }, U.1.1 :=
    Set.Subset.antisymm
      (fun ⟨x, ξ⟩ hp ↦ Set.mem_iUnion.mpr (
        match germ_exist ℱ x ξ with
        | ⟨U, hxU, s, hξ⟩ =>
          let morph := Opens.infLELeft U Vo
          let s' := ℱ.map morph.op s
          let O := basicSet (U ⊓ Vo) s'
          have hO1 : O ∈ basis ℱ := Set.mem_setOf_eq ▸ ⟨(U ⊓ Vo), s', rfl⟩
          have hO2 : proj '' (Subtype.mk O hO1).1 ⊆ V :=
            Set.image_subset_iff.mpr fun _ hq ↦ Set.mem_preimage.mpr hq.1.2
          have hxUVo : x ∈ U ⊓ Vo := Opens.mem_inf.mpr ⟨hxU, Set.mem_preimage.mp hp⟩

          ⟨⟨⟨O, hO1⟩, hO2⟩, hxUVo, hξ ▸ germ_res ℱ morph x hxUVo ▸
            ConcreteCategory.comp_apply _ _ _⟩))

      fun T ⟨U'', ⟨U, (hU : ↑↑U = U'')⟩, hT⟩ ↦
        Set.mem_preimage.mpr (U.2 ((Set.mem_image proj U.1.1 (proj T)).mpr ⟨T, ⟨hU ▸ hT, rfl⟩⟩))

  h ▸ isOpen_iUnion fun U ↦ isOpen_generateFrom_of_mem U.1.2



def proj_continuousMap : ContinuousMap (EtaleSpace ℱ) X :=
  ⟨proj, proj_continuous⟩


def ofHom_proj (ℱ : X.Presheaf C) : obj ℱ ⟶ X :=
  TopCat.ofHom proj_continuousMap



open Classical in

/-- Local homeomorphism structure on the projection. -/
def projIsLocalHomeomorph :
    IsLocalHomeomorph (proj (ℱ := ℱ)) :=
  by
    intro ⟨x, ξ⟩
    match germ_exist ℱ x ξ with
    | ⟨U, hxU, s, h_germ_concrete⟩ =>
      let W := basicSet U s
      let inv_on_U (u : U) : EtaleSpace ℱ := ⟨u.1, germ ℱ U u.1 u.2 s⟩
      let UorIgnore y : U := if hyU : y ∈ U then ⟨y, hyU⟩ else ⟨x, hxU⟩
      let invFun y := inv_on_U (UorIgnore y)
      have UorIgnore_of_mem (u : U) : UorIgnore u.1 = u := dif_pos u.2


      let f : OpenPartialHomeomorph (EtaleSpace ℱ) X := {
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
              ⟨⟨y, germ ℱ U y hyU s⟩, ⟨Set.mem_setOf_eq ▸ ⟨hyU, rfl⟩, rfl⟩⟩)
            : proj '' W = U.1
          ) ▸ U.2

        continuousOn_toFun := continuousOn_iff_continuous_restrict.mpr
          (Continuous.comp proj_continuous continuous_subtype_val)

        continuousOn_invFun := by
          apply continuousOn_iff_continuous_restrict.mpr
          apply (IsTopologicalBasis.continuous_iff (basis_isBasis ℱ)).mpr
          intro A ⟨V, t, hA⟩
          rw [← hA]
          apply isOpen_iff_forall_mem_open.mpr
          intro a ⟨ha, hst⟩
          match germ_eq ℱ (UorIgnore a).1 (UorIgnore a).2 ha s t hst with
          | ⟨A, hA, au, av, hst⟩ =>
          use { b | ↑(UorIgnore ↑b) ∈ A }
          split_ands
          · exact fun ⟨p, p', ⟨hpU, hp2⟩, hp⟩ hpA ↦ ⟨av.le hpA, germ_ext ℱ A hpA au av hst⟩
          · have r : { b : ↑(proj '' W) | ↑(UorIgnore b) ∈ A } = Subtype.val ⁻¹' A := by
              apply Set.Subset.antisymm
              · intro p hp
                match (Set.mem_image proj W ↑p).mp p.2 with
                | ⟨_, ⟨hwU, _⟩, hwp⟩ =>
                have hhh''' := Set.mem_preimage.mpr
                  (UorIgnore_of_mem ⟨↑p, hwp ▸ hwU⟩ ▸ Set.mem_setOf_eq ▸ hp)
                exact hhh'''
              · exact fun p hp ↦ Set.mem_setOf_eq ▸
                  UorIgnore_of_mem ⟨↑p, au.le hp⟩ ▸ Set.mem_preimage.mp hp
            exact r ▸ IsOpen.preimage continuous_subtype_val A.2
          · exact hA
      }

      exact ⟨f, Set.mem_setOf_eq ▸ ⟨hxU, h_germ_concrete ▸ rfl⟩, rfl⟩




end EtaleSpace

end Sheaf

end TopCat
