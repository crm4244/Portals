import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Order


namespace TopCat
namespace Sheaf


open CategoryTheory Opposite Presheaf Topology TopologicalSpace
attribute [local instance] Types.instFunLike Types.instConcreteCategory


universe u
variable {X : TopCat}


/-- Total space of stalks of a presheaf of Type us. -/
def EtaleSpace (F : X.Presheaf (Type u)) := Σ x : X, stalk F x


namespace EtaleSpace
variable {F : X.Presheaf (Type u)}


def proj : EtaleSpace F → X := Sigma.fst


def basicSet (U : Opens X) (s : F.obj (op U)) : Set (EtaleSpace F) :=
  { p | ∃ hp : p.1 ∈ U, p.2 = germ F U p.1 hp s }


variable (F)




def basis : Set (Set (EtaleSpace F)) :=
  { basicSet U s | (U : Opens X) (s : F.obj (op U)) }


instance topology : TopologicalSpace (EtaleSpace F) :=
  generateFrom (basis F)


def obj (F : X.Presheaf (Type u)) : TopCat := @TopCat.of (EtaleSpace F) (topology F)


instance basis_isBasis : IsTopologicalBasis (basis F) :=
  {
    exists_subset_inter := fun _ ⟨_, sU, hU⟩ _ ⟨_, sV, hV⟩ ⟨p, _⟩ ⟨mU, mV⟩ ↦
      have ⟨W, hpW, hWU, hWV, hW⟩ := F.germ_eq p (hU ▸ mU).1 (hV ▸ mV).1 sU sV
        ((hU ▸ mU).2.symm.trans (hV ▸ mV).2)
      ⟨basicSet W ((ConcreteCategory.hom (F.map hWU.op)) sU),
        ⟨W, _, rfl⟩,
        ⟨hpW, (hU ▸ mU).2.trans <| congr_fun (F.germ_res hWU p hpW).symm sU⟩,
        fun ⟨q, _⟩ ⟨m, h⟩ ↦ ⟨
          hU ▸ ⟨hWU.le m, h.trans <| congr_fun (F.germ_res hWU q m) sU⟩,
          hV ▸ ⟨hWV.le m, h.trans <| (congr_arg (F.germ W q m) hW).trans <|
            congr_fun (F.germ_res hWV q m) sV⟩⟩⟩
    sUnion_eq := Set.eq_univ_of_forall fun ⟨p, ξ⟩ ↦
      have ⟨U, hpU, s, h⟩ := F.germ_exist p ξ
      Set.mem_sUnion.mpr  ⟨basicSet U s, ⟨U, s, rfl⟩, hpU, h.symm⟩
    eq_generateFrom := rfl
  }




theorem proj_continuous {F : X.Presheaf (Type u)} :
    @Continuous (EtaleSpace F) X (topology F) X.str proj :=
  Continuous.mk fun V hV ↦
  let Vo : Opens X := ⟨V, hV⟩
  have h : proj ⁻¹' V = ⋃ U : { U : basis F // proj '' U.1 ⊆ V }, U.1.1 := by
    apply Set.Subset.antisymm
      (fun ⟨x, ξ⟩ hp ↦ Set.mem_iUnion.mpr (
        match germ_exist F x ξ with
        | ⟨U, hxU, s, hξ⟩ =>
          let morph := Opens.infLELeft U Vo
          let s' := F.map morph.op s
          let O := basicSet (U ⊓ Vo) s'
          have hO1 : O ∈ basis F := Set.mem_setOf_eq ▸ ⟨(U ⊓ Vo), s', rfl⟩
          have hO2 : proj '' (Subtype.mk O hO1).1 ⊆ V :=
            Set.image_subset_iff.mpr fun _ hq ↦ Set.mem_preimage.mpr hq.1.2
          have hxUVo : x ∈ U ⊓ Vo := Opens.mem_inf.mpr ⟨hxU, Set.mem_preimage.mp hp⟩

          ⟨⟨⟨O, hO1⟩, hO2⟩, hxUVo, hξ ▸ germ_res F morph x hxUVo ▸ by rfl⟩))

    · exact fun T ⟨U'', ⟨U, (hU : ↑↑U = U'')⟩, hT⟩ ↦
        Set.mem_preimage.mpr (U.2 ((Set.mem_image proj U.1.1 (proj T)).mpr ⟨T, ⟨hU ▸ hT, rfl⟩⟩))

  h ▸ isOpen_iUnion fun U ↦ isOpen_generateFrom_of_mem U.1.2



def proj_continuousMap {F : X.Presheaf (Type u)} : ContinuousMap (EtaleSpace F) X :=
  ⟨proj, proj_continuous⟩


def ofHom_proj (F : X.Presheaf (Type u)) : obj F ⟶ X :=
  TopCat.ofHom proj_continuousMap



open Classical in

/-- Local homeomorphism structure on the projection. -/
def projIsLocalHomeomorph {F : X.Presheaf (Type u)} :
    IsLocalHomeomorph (proj (F := F)) :=
  by
    intro ⟨x, ξ⟩
    match germ_exist F x ξ with
    | ⟨U, hxU, s, h_germ_concrete⟩ =>
      let W := basicSet U s
      let inv_on_U (u : U) : EtaleSpace F := ⟨u.1, germ F U u.1 u.2 s⟩
      let UorIgnore y : U := if hyU : y ∈ U then ⟨y, hyU⟩ else ⟨x, hxU⟩
      let invFun y := inv_on_U (UorIgnore y)
      have UorIgnore_of_mem (u : U) : UorIgnore u.1 = u := dif_pos u.2


      let f : OpenPartialHomeomorph (EtaleSpace F) X := {
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
              ⟨⟨y, germ F U y hyU s⟩, ⟨Set.mem_setOf_eq ▸ ⟨hyU, rfl⟩, rfl⟩⟩)
            : proj '' W = U.1
          ) ▸ U.2

        continuousOn_toFun := continuousOn_iff_continuous_restrict.mpr
          (Continuous.comp proj_continuous continuous_subtype_val)

        continuousOn_invFun := by
          unfold proj invFun inv_on_U
          apply continuousOn_iff_continuous_restrict.mpr
          apply continuous_generateFrom_iff.mpr
          rintro _ ⟨V, t, rfl⟩
          apply isOpen_induced_iff.mpr
          unfold Set.restrict
          simp only
          have hxV : x ∈ V := sorry
          #check isOpen_generateFrom_of_mem
          #check generateFrom
          have b : Opens.IsBasis ((fun U : basis F ↦
              ⟨U.1, isOpen_generateFrom_of_mem U.2⟩) '' Set.univ) := by
            sorry
          #check germ_eq_of_isBasis sorry F x hxU hxV sorry
          #check germ_res
          use V
          split_ands
          · exact V.2
          · apply Set.Subset.antisymm
            · rintro ⟨_, ⟨y, μ⟩, ⟨hyU : y ∈ U,
                hp_germ⟩, rfl⟩ _hyV
              have hyV : y ∈ V := Set.mem_preimage.mp _hyV
              apply Set.mem_preimage.mpr
              unfold basicSet
              --rw [Set.restrict_apply]
              rw [UorIgnore_of_mem ⟨y, hyU⟩]
              rw [Set.mem_setOf_eq]
              use hyV

              simp only
              rw [(rfl : (Subtype.mk y hyU).2 = hyU)]
              rw [← germ_res F (Opens.infLELeft U V) y ⟨hyU, hyV⟩]
              rw [← germ_res F (Opens.infLERight U V) y ⟨hyU, hyV⟩]

              simp
              apply congrArg
              #check germ_res_apply

              sorry


            · rintro ⟨_, ⟨y, μ⟩, ⟨hyU : y ∈ U,
                hp_germ : μ = germ F U y hyU s⟩, rfl⟩ ⟨h, _⟩
              apply Set.mem_preimage.mpr
              simp only [Set.restrict_apply] at ⊢ h
              have h := SetLike.mem_coe.mpr (UorIgnore_of_mem ⟨y, hyU⟩ ▸ h)
              exact h
      }

      exact ⟨f, Set.mem_setOf_eq ▸ ⟨hxU, h_germ_concrete ▸ rfl⟩, rfl⟩



def proj_isOpenMap {F : X.Presheaf (Type u)} :
    IsOpenMap (proj (F := F)) := by

  sorry



/-- The projection is an étale map. -/
def proj_isEtale {X : TopCat} {F : X.Presheaf (Type u)} :
    IsOpenMap (proj (F := F)) ∧ IsLocalHomeomorph (proj (F := F)) :=
  ⟨proj_isOpenMap, projIsLocalHomeomorph⟩



end EtaleSpace
