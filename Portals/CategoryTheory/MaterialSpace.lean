
import Mathlib.Algebra.Group.End
import Portals.CategoryTheory.PortalMap
import Portals.CategoryTheory.GluingPattern


variable {X : Type} [TopologicalSpace X] {S : Set X}


namespace Portal






def union_surface (F : Set (PortalMap S)) : Set X := ⋃ f : F, f.1.surface_copy


variable {F : Set (PortalMap S)}



theorem surface_copy_subset_union_surface (f : F) :
    f.1.surface_copy ⊆ union_surface F :=
  fun _ h ↦ Set.mem_iUnion.mpr ⟨f, h⟩


def restrict_union_surface (f : F) : Set (Set.range f.1) :=
  Sides.restrict_surface (union_surface F) (Set.range f.1)


theorem surface_copy_subset_union_surface_restrict (f : F) :
    f.1.restricted_surface_copy ⊆ restrict_union_surface f :=
  fun _ h ↦ Set.mem_preimage.mpr (surface_copy_subset_union_surface f (Set.mem_preimage.mp h))



def restricted_union_side_to_original {f : F} (σ : Sides (restrict_union_surface f)) : Sides S :=
  (f.1.map_sides_inv (Sides.subsurface_colift
    (surface_copy_subset_union_surface_restrict f) σ)).lift


theorem center_rusto_comm {f : F} (σ : Sides (restrict_union_surface f)) :
    (restricted_union_side_to_original σ).center = f.1.inv_range (σ.center) :=
  Sides.subsurface_colift_comm (surface_copy_subset_union_surface_restrict f) σ ▸
    f.1.map_sides_inv_comm _ ▸ Sides.lift_comm _ _


theorem center_eq_of_rusto {f : F} {a b : Sides (restrict_union_surface f)}
  (hab : a.center = b.center) :
    (restricted_union_side_to_original a).center = (restricted_union_side_to_original b).center :=
  center_rusto_comm a ▸ center_rusto_comm b ▸ hab ▸ rfl



def recommendation (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface f) (Equiv.Perm F) where
  map := fun hab ↦ γ (center_eq_of_rusto hab)
  trans hab hbc := γ.trans (center_eq_of_rusto hab) (center_eq_of_rusto hbc)

-- might want to check if the recommendation is locally consistent. not important yet




section CompositionConstruction





end CompositionConstruction



end Portal
