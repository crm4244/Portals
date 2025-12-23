

import Mathlib.Topology.Sets.Opens
import Portals.CategoryTheory.SideSpace

open Topology TopologicalSpace


variable {X : Type} [TopologicalSpace X]





namespace Portal



class PortalMap (S : Set X) where
  domain : Opens X
  map : domain → X
  surface_subset : S ⊆ domain
  isOpenEmbedding : IsOpenEmbedding map

instance (S : Set X) : CoeFun (PortalMap S) (fun P ↦ P.domain → X) := {coe P := P.map}




namespace PortalMap

variable {S : Set X}


def restricted_surface (f : PortalMap S) : Set f.domain := Sides.restrict_surface S f.domain
def surface_copy (f : PortalMap S) : Set X := f '' f.restricted_surface
def restricted_surface_copy (f : PortalMap S) : Set (Set.range f) :=
  Sides.restrict_surface f.surface_copy (Set.range f)



def map_sides {f : PortalMap S} :
    Sides f.restricted_surface → Sides f.surface_copy :=
  Sides.map (S := f.restricted_surface) f.isOpenEmbedding


theorem map_sides_comm {f : PortalMap S} (σ : Sides f.restricted_surface) :
  (f.map_sides σ).center = f σ.center := Sides.map_comm f.isOpenEmbedding σ



noncomputable def homeomorph (f : PortalMap S) :
    Homeomorph (Set.univ : Set f.domain) (Set.range f) :=
  Set.image_univ ▸ f.isOpenEmbedding.homeomorphImage Set.univ

noncomputable def inv_range (f : PortalMap S) (p : Set.range f) : f.domain :=
  ⇑f.homeomorph.symm p

theorem isOpenEmbedding_invRange (f : PortalMap S) : IsOpenEmbedding f.inv_range :=
  IsOpenEmbedding.comp isOpen_univ.isOpenEmbedding_subtypeVal (Homeomorph.isOpenEmbedding _)


def map_sides_inv {f : PortalMap S} : Sides f.restricted_surface_copy →
    Sides (restricted_surface f) :=
  Sides.map (S := f.restricted_surface_copy) f.isOpenEmbedding_invRange


theorem map_sides_inv_comm {f : PortalMap S} (σ : Sides (f.restricted_surface_copy)) :
    (f.map_sides_inv σ).center = f.inv_range σ.center :=
  Sides.map_comm f.isOpenEmbedding_invRange σ



end PortalMap





end Portal
