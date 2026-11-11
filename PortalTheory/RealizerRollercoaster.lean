import PortalTheory.GluingPattern
import PortalTheory.Rollercoaster.Basic


open Portal

variable {α G : Type*} [TopologicalSpace α] [Group G] {S : Set α}


-- a Rollercoaster with ComponentRealizer data bundled on the regions
structure RespectedRealizerRollercoaster (γ : GluingPattern S G) (a b : α) where
  coaster : Rollercoaster ⊤ a b
  isOpen_region (i : Fin coaster.regions.length) : IsOpen (X := α) coaster.regions[i]
  get_hub (i : Fin coaster.regions.length) : α
  get_realizer (i : Fin coaster.regions.length) :
    ComponentRealizer ⟨coaster.regions[i], isOpen_region i⟩ S (get_hub i)
  respects_realizer (i : Fin coaster.regions.length) : γ.respects_realizer (get_realizer i)
