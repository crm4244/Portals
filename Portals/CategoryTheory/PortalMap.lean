

import Mathlib.Topology.Sets.Opens
import Portals.CategoryTheory.SideSpace

open Topology TopologicalSpace







namespace Portal




variable (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]

def PortalMap : Type := {f : X → Y // IsOpenEmbedding f}

instance : CoeFun (PortalMap X Y) (fun _ ↦ X → Y) := {coe f := f.1}




namespace PortalMap

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (f : PortalMap X Y)




def range : Set Y := Set.range f
def opens_range : Opens Y := ⟨f.range, f.2.isOpen_range⟩


def restricted_image (S : Set X) : Set f.range :=
  Sides.restrict_surface (f '' S) f.range


noncomputable def homeomorph : Homeomorph (⊤ : Set X) f.range :=
  by apply Set.image_univ ▸ f.2.homeomorphImage ⊤


noncomputable def inv_range (p : f.range) : X := f.homeomorph.symm p

theorem isOpenEmbedding_invRange : IsOpenEmbedding (f.inv_range) :=
  IsOpenEmbedding.comp isOpen_univ.isOpenEmbedding_subtypeVal (Homeomorph.isOpenEmbedding _)


def map_sides_inv (S : Set X) : Sides (restricted_image f S) → Sides S :=
  Sides.map (S := restricted_image f S) f.isOpenEmbedding_invRange


theorem map_sides_inv_comm (S : Set X) (σ : Sides (restricted_image f S)) :
    (f.map_sides_inv S σ).center = f.inv_range σ.center :=
  Sides.map_comm f.isOpenEmbedding_invRange σ






end PortalMap

end Portal
