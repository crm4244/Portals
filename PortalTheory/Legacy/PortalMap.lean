import Portals.Surface
import Mathlib.Topology.Basic


variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X] [hX3 : LocallyConnectedSpace X]



class PortalMap (S : Set X) where
  domain : Set X
  isOpen_domain : IsOpen domain
  closure_subset_domain : closure S ⊆ domain
  map : domain → X
  isOpenEmbedding_map : Topology.IsOpenEmbedding map
  -- also the map is an isomorphism on its image, for some sense of isomorphism

namespace PortalMap


--theorem homeomorph (S : Set X) (f : PortalMap S) : Homeomorph f.map

def instPortalMap_identity (S : Set X) {U : Set X} (hU : IsOpen U) (hUS : closure S ⊆ U) :
  PortalMap S := {
    domain := U
    isOpen_domain := hU
    closure_subset_domain := hUS
    map := Subtype.val
    isOpenEmbedding_map := IsOpen.isOpenEmbedding_subtypeVal hU
  }


open Classical in def instSurface {S : Set X} [hS : Surface S] (f : PortalMap S) :
  Surface (f.map '' (Subtype.val ⁻¹' S)) :=
  let fS := f.map '' (Subtype.val ⁻¹' S)
  {
    surjective_center := by
      -- use the lift
      #check IsOpen.isOpenEmbedding_subtypeVal
      #check Topology.IsInducing
      sorry
    realizer := fun p ↦
      let R := hS.realizer p
      let U := R.set ∩ if p ∈ Set.range f.map then Set.range f.map else (closure fS)ᶜ
      have hU : IsOpen U := IsOpen.inter R.isOpen (dite (p ∈ Set.range f.map)
        (fun h ↦ if_pos h ▸ f.isOpenEmbedding_map.isOpen_range)
        (fun h ↦ if_neg h ▸ isOpen_compl_iff.mpr isClosed_closure))
      have hpU : p ∈ U := ⟨R.origin_mem, dite (p ∈ Set.range f.map)
        (fun h ↦ if_pos h ▸ h)
        (fun h ↦ if_neg h ▸ by
          apply Set.compl_subset_compl.mpr
          #check Set.image_mono f.closure_subset_domain
          #check Topology.IsInducing.closure_eq_preimage_closure_image f.isOpenEmbedding_map.isInducing (Subtype.val ⁻¹' S)
          sorry)⟩
      let R' := Surface.Realizer.instInter R hU hpU
      {
        preRealizer := R'.preRealizer
        bijective_toComponent_of_center_eq_origin := by

          sorry
      }
  }



-- define the lift of a portal map into side space
-- theorem: a restriction of a portal map to another
  -- portal map with a smaller domain has the same side-space lift
