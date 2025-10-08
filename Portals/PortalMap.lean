import Portals.Surface
import Mathlib.Topology.Basic


variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X]



class PortalMap (S : Set X) where
  domain : Set X
  surface_subset_domain : S ⊆ domain
  isOpen_domain : IsOpen domain
  map : Subtype domain → X
  -- also the map is an isomorphism on its image, for some sense of isomorphism


-- define the lift of a portal map into side space
-- theorem: a restriction of a portal map to another
  -- portal map with a smaller domain has the same side-space lift
