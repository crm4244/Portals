import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Portals.CategoryTheory.PortalMap
import Portals.CategoryTheory.GluingPattern



universe u v


namespace Portal


variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {F : Set (PortalMap X Y)} {S : Set Y}

def union_surface (F : Set (PortalMap X Y)) (S : Set Y) : Set X := ⋃ f : F, f '' S
abbrev 𝒮 (F : Set (PortalMap X Y)) := union_surface F


abbrev 𝒮_restrict (S : Set Y) (f : F) : Set f.1.range :=
  Sides.restrict_surface (𝒮 F S) f.1.range


theorem surface_copy_subset_union_surface (f : F) : f.1 '' S ⊆ 𝒮 F S :=
  fun _ ↦ (Set.mem_iUnion.mpr ⟨f, ·⟩)


theorem surface_copy_subset_union_surface_restrict (f : F) :
  Sides.restrict_surface (f.1 '' S) f.1.range ⊆ (𝒮_restrict S f) := fun _ ↦
    (Set.mem_preimage.mpr <| surface_copy_subset_union_surface f <| Set.mem_preimage.mp ·)


def restricted_union_side_to_original {f : F} (σ : Sides (𝒮_restrict S f)) : Sides S :=
  f.1.map_sides_inv (Sides.subsurface_colift
    (surface_copy_subset_union_surface_restrict f) σ)


theorem center_rusto_comm {f : F} (σ : Sides (𝒮_restrict S f)) :
    (restricted_union_side_to_original σ).center = f.1.inv (σ.center) :=
  Sides.subsurface_colift_comm (surface_copy_subset_union_surface_restrict f) σ ▸
    f.1.map_sides_inv_comm _


/-
theorem center_eq_of_rusto {f : F} (a b : Sides (restrict_union_surface S f))
  (hab : a.center = b.center := by aesop) :
    (restricted_union_side_to_original a).center = (restricted_union_side_to_original b).center :=
  (hab ▸ center_rusto_comm a).trans (center_rusto_comm b).symm


theorem center_eq_of_usto {f : F} (a b : Sides (union_surface S F))
  (hab : a.center = b.center := by aesop) (h_mem : a.center ∈ f.1.opens_range := by aesop) :
    a.restrict_of_mem.center = b.restrict_of_mem.center :=
  Set.injOn_subtype_val (Set.mem_univ _) (Set.mem_univ _)
    (a.restrict_comm.trans <| hab.trans b.restrict_comm.symm)
-/


def rusto_at_of_at {f : F} {p : f.1.range} (σ : Sides.at_point (𝒮_restrict S f) p) :
  Sides.at_point S (f.1.inv p) :=
    ⟨restricted_union_side_to_original σ.1,
      Set.mem_setOf_eq.mpr (center_rusto_comm σ.1 ▸ congr_arg f.1.inv σ.2)⟩

/-
noncomputable def usto_at_of_at {f : F} {p : f.1.opens_range} (σ : Sides.at_point (𝒮 F S) p.1) :
  Sides.at_point S (f.1.inv_range p) :=
    rusto_at_of_at ⟨_, Set.mem_setOf_eq.mpr <| Subtype.val_injective <|
      (congr_arg Subtype.val <| σ.1.center_restrict_comm <| σ.2.symm ▸ p.2).trans σ.2⟩
-/

noncomputable def recommendation_gluing_pattern (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (𝒮_restrict S f) (Equiv.Perm F) where
  map a b := γ (rusto_at_of_at a) (rusto_at_of_at b)
  trans _ _ _ := γ.trans _ _ _

-- might want to check if the recommendation_gluing_pattern is locally consistent. not important yet


noncomputable def recommendation_map (γ : GluingPattern S (Equiv.Perm F))
  {f : F} {p : f.1.opens_range} (a b : Sides.at_point (𝒮 F S) p.1) :
    Equiv.Perm F :=
  recommendation_gluing_pattern γ f (Sides.restricted_at_of_at p.2 a) (Sides.restricted_at_of_at p.2 b)



section relevant

open TopologicalSpace



def relevant_portal_maps (F : Set (PortalMap X Y)) (p : X) : Type max u v :=
  { f : F // p ∈ f.1.range }


variable (γ : GluingPattern S (Equiv.Perm F))


def relevant_perms (p : X) : Subgroup (Equiv.Perm F) := Subgroup.closure
  {P : Equiv.Perm F | ∃ (f : relevant_portal_maps F p)
    (a b : Sides.at_point (𝒮 F S) (Subtype.mk p f.2)),
      recommendation_map γ a b = P}


noncomputable def relevant_recommendation_map {p : X} (f : relevant_portal_maps F p)
  (a b : Sides.at_point (𝒮 F S) (Subtype.mk p f.2)) :
    relevant_perms γ p :=
  ⟨recommendation_map γ a b, Subgroup.mem_closure_of_mem <| Set.mem_setOf_eq.mpr ⟨f, a, b, rfl⟩⟩


def irrelevants_locally_trivial : Prop :=
  ∀ (p : X), ∃ (U : Opens X) (_ : p ∈ U), ∀ {f : F}, p ∉ f.1.range →
    (recommendation_gluing_pattern γ f).is_trivial_on (Subtype.val ⁻¹' U)



end relevant


end Portal
