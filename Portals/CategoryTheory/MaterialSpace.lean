
import Mathlib.Algebra.Group.End
import Portals.CategoryTheory.PortalMap
import Portals.CategoryTheory.GluingPattern


variable {X : Type} [TopologicalSpace X] {S : Set X}


namespace Portal






def union_surface (F : Set (PortalMap S)) : Set X :=
  ⋃ f : F, {f.1 ⟨x, f.1.surface_subset x.2⟩ | x : S}


variable {F : Set (PortalMap S)}



theorem surface_copy_subset_union_surface (f : F) :
    f.1.surface_copy ⊆ union_surface F :=
  fun _ h ↦ Set.mem_iUnion.mpr ⟨f, h⟩


def restrict_union_surface (f : F) : Set (Set.range f.1) :=
  Sides.restrict_surface (union_surface F) (Set.range f.1)


--#check Sides.


def union_side_to_original {f : F} {σ : Sides (restrict_union_surface f)}
    (hσ : σ.center.1 ∈ Set.range f.1) : Sides S :=
  sorry


-- might need this: [RealizingSurface (union_surface F)]
-- gotta restrict to f.1.domain
def recommendation (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface f) (Equiv.Perm F) where
  map := fun {a b} _ ↦ by
    --#check fun x ↦ Sides.lift S f.1.domain ∘ union_side_to_original
    #check γ (sorry : )
    #check a.center.property
    sorry--(sorry : (union_side_to_original a.center.property).center = (union_side_to_original b.center.property).center)
  trans := sorry




end Portal
