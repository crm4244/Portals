

import Mathlib.Topology.Sets.Opens
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


def surface_copy (f : PortalMap S) : Set X :=
  {f ⟨x, f.surface_subset x.2⟩ | x : S}


-- we need the lift to sides of the copy and its inverse




end PortalMap



end Portal
