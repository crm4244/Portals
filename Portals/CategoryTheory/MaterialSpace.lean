
import Mathlib.Algebra.Group.End
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Portals.CategoryTheory.PortalMap
import Portals.CategoryTheory.GluingPattern


variable {X : Type} [TopologicalSpace X] {S : Set X}


namespace Portal






def union_surface (F : Set (PortalMap S)) : Set X := ⋃ f : F, f.1.surface_copy


variable {F : Set (PortalMap S)}


theorem surface_copy_subset_union_surface (f : F) :
    f.1.surface_copy ⊆ union_surface F :=
  fun _ h ↦ Set.mem_iUnion.mpr ⟨f, h⟩


def restrict_union_surface (f : F) : Set f.1.range :=
  Sides.restrict_surface (union_surface F) f.1.range


theorem surface_copy_subset_union_surface_restrict (f : F) :
    f.1.restricted_surface_copy ⊆ restrict_union_surface f :=
  fun _ h ↦ Set.mem_preimage.mpr (surface_copy_subset_union_surface f (Set.mem_preimage.mp h))



def restricted_union_side_to_original {f : F} (σ : Sides (restrict_union_surface f)) : Sides S :=
  (f.1.map_sides_inv (Sides.subsurface_colift
    (surface_copy_subset_union_surface_restrict f) σ)).lift


theorem center_rusto_comm {f : F} (σ : Sides (restrict_union_surface f)) :
    (restricted_union_side_to_original σ).center = f.1.inv_range (σ.center) :=
  Sides.subsurface_colift_comm (surface_copy_subset_union_surface_restrict f) σ ▸
    f.1.map_sides_inv_comm _ ▸ Sides.lift_comm _


theorem center_eq_of_rusto {f : F} {a b : Sides (restrict_union_surface f)}
  (hab : a.center = b.center) :
    (restricted_union_side_to_original a).center = (restricted_union_side_to_original b).center :=
  center_rusto_comm a ▸ center_rusto_comm b ▸ hab ▸ rfl




def recommendation_gluing_pattern (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface f) (Equiv.Perm F) where
  map := fun hab ↦ γ (center_eq_of_rusto hab)
  trans hab hbc := γ.trans (center_eq_of_rusto hab) (center_eq_of_rusto hbc)

-- might want to check if the recommendation_gluing_pattern is locally consistent. not important yet


noncomputable def recommendation_map (γ : GluingPattern S (Equiv.Perm F)) {f : F} {p : X}
  (hp : p ∈ f.1.range) {a b : Sides (union_surface F)} (ha : a.center = p) (hb : b.center = p) :
    Equiv.Perm F :=
  sorry --recommendation_gluing_pattern γ f (center_eq_of_restrict_union_side (hb ▸ ha) (ha ▸ hp))







namespace composition_construction

variable [TopologicalSpace (Equiv.Perm F)]
variable [CommMonoid (Equiv.Perm F)] -- this is a really strict condition
variable [RealizingSurface (union_surface F)]


--variable [RealizingSurface (union_surface F)]

def relevant (F : Set (PortalMap S)) (p : X) : Set F := { f | p ∈ f.1.range }


noncomputable def composedGluingattern (γ : GluingPattern S (Equiv.Perm F)) :
    GluingPattern (union_surface F) (Equiv.Perm F) where
  map {a b} hab := ∏' f : relevant F a.center, (recommendation_map γ f.2 rfl hab.symm)
  trans := by
    intro a b c
    sorry

theorem composedGluingattern_isLocallyConsistent (γ : GluingPattern S (Equiv.Perm F)) :
    (composedGluingattern γ).isLocallyConsistent := by

  sorry


#check Multipliable

end composition_construction






section EqualityConstruction


def recommendations_agree (γ : GluingPattern S (Equiv.Perm F)) :
-- use the intersection f.1.1.domain ∩ g.1.1.domain
    ∀ (p : X) (f g : { x : F | p ∈ x.1.range }), recommendation γ f = recommendation γ g :=
  sorry


end EqualityConstruction



end Portal
