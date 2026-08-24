import Mathlib.Topology.Sets.Opens
import Portals.CategoryTheory.Sides

open Topology TopologicalSpace






namespace Portal



def PortalMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :
  Type _ := {f : Y → X // IsOpenEmbedding f}


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance : CoeFun (PortalMap X Y) (fun _ ↦ Y → X) := {coe f := f.1}



namespace PortalMap

variable (f : PortalMap X Y)




def range : Set X := Set.range f
def opens_range : Opens X := ⟨f.range, f.2.isOpen_range⟩


noncomputable def homeomorph : Homeomorph (⊤ : Set Y) f.range :=
  (f.2.homeomorphImage ⊤).trans (Homeomorph.setCongr Set.image_univ)

noncomputable def inv {f : PortalMap X Y} : f.range → Y := Subtype.val ∘ f.homeomorph.symm


theorem inv_left (p : Y) : f.inv ⟨f p, Set.mem_range_self _⟩ = p :=
  congr_arg Subtype.val <| f.homeomorph.symm_apply_apply ⟨p, Set.mem_univ p⟩


theorem inv_right (y : f.range) : f (f.inv y) = y :=
  congr_arg Subtype.val <| f.homeomorph.apply_symm_apply y


theorem isOpenEmbedding_invRange : IsOpenEmbedding (f.inv) :=
  isOpen_univ.isOpenEmbedding_subtypeVal.comp f.homeomorph.symm.isOpenEmbedding


theorem isEmbedding_invRange : IsEmbedding (f.inv) :=
  f.isOpenEmbedding_invRange.isEmbedding


def map_sides_inv {S : Set X} : Sides (Sides.restrict_surface S f.range) → Sides (f ⁻¹' S)
  | σ => σ.map f.isEmbedding_invRange


theorem map_sides_inv_comm {S : Set X} (σ : Sides (Sides.restrict_surface S f.range)) :
  (f.map_sides_inv σ).center = f.inv σ.center :=
    σ.map_comm f.isEmbedding_invRange






end PortalMap

end Portal
