
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Portals.CategoryTheory.PortalMap
import Portals.CategoryTheory.GluingPattern




namespace Portal


variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable (S : Set Y)
variable {F : Set (PortalMap Y X)}


def union_surface (F : Set (PortalMap Y X)) : Set X := ⋃ f : F, f '' S



theorem surface_copy_subset_union_surface (f : F) :
    f.1 '' S ⊆ union_surface S F :=
  fun _ h ↦ Set.mem_iUnion.mpr ⟨f, h⟩


def restrict_union_surface (f : F) : Set f.1.range :=
  Sides.restrict_surface (union_surface S F) f.1.range


theorem surface_copy_subset_union_surface_restrict (f : F) :
    f.1.restricted_image S ⊆ restrict_union_surface S f :=
  fun _ h ↦ Set.mem_preimage.mpr (surface_copy_subset_union_surface S f (Set.mem_preimage.mp h))



variable {S : Set Y}



def restricted_union_side_to_original {f : F} (σ : Sides (restrict_union_surface S f)) : Sides S :=
  f.1.map_sides_inv S (Sides.subsurface_colift
    (surface_copy_subset_union_surface_restrict S f) σ)


theorem center_rusto_comm {f : F} (σ : Sides (restrict_union_surface S f)) :
    (restricted_union_side_to_original σ).center = f.1.inv_range (σ.center) :=
  Sides.subsurface_colift_comm (surface_copy_subset_union_surface_restrict S f) σ ▸
    f.1.map_sides_inv_comm S _


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


def rusto_at_of_at {f : F} {p : f.1.range} (σ : Sides.at_point (restrict_union_surface S f) p) :
  Sides.at_point S (f.1.inv_range p) :=
    ⟨restricted_union_side_to_original σ.1,
      Set.mem_setOf_eq.mpr (center_rusto_comm σ.1 ▸ congr_arg f.1.inv_range σ.2)⟩


noncomputable def usto_at_of_at {f : F} {p : f.1.opens_range}
  (σ : Sides.at_point (union_surface S F) p) :
    Sides.at_point S (f.1.inv_range p) :=
  rusto_at_of_at ⟨_, Set.mem_setOf_eq.mpr <| Subtype.val_injective <|
    (congr_arg Subtype.val <| σ.1.center_restrict_comm <| σ.2.symm ▸ p.2).trans σ.2⟩


noncomputable def recommendation_gluing_pattern (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface S f) (Equiv.Perm F) where
  map a b := γ (rusto_at_of_at a) (rusto_at_of_at b)
  trans _ _ _ := γ.trans _ _ _

-- might want to check if the recommendation_gluing_pattern is locally consistent. not important yet


noncomputable def recommendation_map (γ : GluingPattern S (Equiv.Perm F))
  {f : F} {p : f.1.opens_range} (a b : Sides.at_point (union_surface S F) p) :
    Equiv.Perm F :=
  recommendation_gluing_pattern γ f (Sides.restricted_at_of_at a) (Sides.restricted_at_of_at b)








namespace composition_construction

open TopologicalSpace


def relevant_portal_maps (F : Set (PortalMap Y X)) (p : X) : Sort 1 :=
  { f : F // p ∈ f.1.range }


variable (γ : GluingPattern S (Equiv.Perm F))


def relevant_perms (p : X) : Subgroup (Equiv.Perm F) := Subgroup.closure
  {P : Equiv.Perm F | ∃ (f : relevant_portal_maps F p)
    (a b : Sides.at_point (union_surface S F) (Subtype.mk p f.2)),
      recommendation_map γ a b = P}


noncomputable def relevant_recommendation_map {p : X} (f : relevant_portal_maps F p)
  (a b : Sides.at_point (union_surface S F) (Subtype.mk p f.2)) :
    relevant_perms γ p :=
  ⟨recommendation_map γ a b, Subgroup.mem_closure_of_mem <| Set.mem_setOf_eq.mpr ⟨f, a, b, rfl⟩⟩


def irrelevants_locally_trivial : Prop :=
  ∀ (p : X), ∃ (U : Opens X) (_ : p ∈ U), ∀ {f : F}, p ∉ f.1.range →
    (recommendation_gluing_pattern γ f).is_trivial_on (Subtype.val ⁻¹' U)



-- we could change the SummationFilter if we want, using unconditional for now

noncomputable def composedGluingPattern (γ : GluingPattern S (Equiv.Perm F))
  [∀ p, IsMulCommutative (relevant_perms γ p)] [∀ p, TopologicalSpace (relevant_perms γ p)]
  [∀ p, T2Space (relevant_perms γ p)] [∀ p, ContinuousMul (relevant_perms γ p)]
  (h_multipliable : ∀ {p : X} (a b : Sides.at_point (union_surface S F) p),
    Multipliable (relevant_recommendation_map γ · a b) := by assumption) :
      GluingPattern (union_surface S F) (Equiv.Perm F) where

  map {p} a b := ↑(∏' f : relevant_portal_maps F p,
    relevant_recommendation_map γ f a b)
  trans {p} a b c := by
    rw [← Subgroup.coe_mul]
    apply congr_arg
    rw [← Multipliable.tprod_mul (h_multipliable a b) (h_multipliable b c)]
    apply tprod_congr
    intro f
    rw [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
    apply (recommendation_gluing_pattern γ f.1).trans




theorem composedGluingattern_isLocallyConsistent_iff
  {γ : GluingPattern S (Equiv.Perm F)} (hγ : γ.isLocallyConsistent)
  [∀ p, IsMulCommutative (relevant_perms γ p)]
  [∀ p, TopologicalSpace (relevant_perms γ p)]
  [∀ p, T2Space (relevant_perms γ p)]
  [∀ p, ContinuousMul (relevant_perms γ p)]
  (h_multipliable : ∀ {p : X} (a b : Sides.at_point (union_surface S F) p),
    Multipliable (relevant_recommendation_map γ · a b) := by assumption)
  (hR : ∀ {p U}, p ∈ U → ∃ (V : Opens X) (R : ComponentRealizer V (union_surface S F) p), V ≤ U) :

  (composedGluingPattern γ).isLocallyConsistent ↔
    irrelevants_locally_trivial γ ∧
    ∃ m : Y → Opens Y,
      (∀ p : Y, ∃ R : ComponentRealizer (m p) S p, γ.respects_realizer R) ∧
      (∀ p : X, p ∈ interior (⋂ f : relevant_portal_maps F p,
        f.1.1 '' (m <| f.1.1.inv_range ⟨p, f.2⟩).1)) := by


  apply Iff.intro
  · intro h
    split_ands
    · intro p
      rcases @h p with ⟨U, R, hUR⟩
      use U, R.hub_mem
      unfold GluingPattern.respects_realizer at hUR
      intro f hf
      -- huh this part might be false
      sorry
    · sorry

  · intro ⟨h_trivial, m, hmR, hmf⟩ p
    rcases h_trivial p with ⟨U, hpU, hU⟩
    let I : Opens X := ⟨interior <| ⋂ f : relevant_portal_maps F p,
      f.1 '' (m <| f.1.1.inv_range ⟨p, f.2⟩).1, isOpen_interior⟩
    rcases @hR p (U ⊓ I) ⟨hpU, hmf p⟩ with ⟨V, R, hV_le⟩

    use V, R


    unfold composedGluingPattern GluingPattern.respects_realizer
    simp only

    intro q a b

    let castF : relevant_portal_maps F p → relevant_portal_maps F q := by

      sorry
    have castF_injective : Function.Injective castF := by sorry

    rw [← tprod_extend_one castF_injective
      (relevant_recommendation_map γ · (R.side_transfer_at a) (R.side_transfer_at b))]

    #check tprod_congr
    #check Multipliable.map_tprod
    #check tprod_eq_tprod_of_ne_one_bij
    #check Equiv.tprod_eq_tprod_of_mulSupport
    --show that f : (relevant_portal_maps F q) is either the same as in p, or trivial


    sorry

/-

    #check R.hub_mem


    cases Decidable.em (Nonempty (relevant_portal_maps F p)) with
    | inl h_nonempty =>
      have f := (inhabited_of_nonempty h_nonempty).default
      rcases hγ (p := f.1.1.inv_range ⟨p, f.2⟩) with ⟨Uy, Ry, hy⟩
      have U : Opens X := ⟨f.1.1 '' Uy, f.1.1.2.isOpen_iff_image_isOpen.mp Uy.2⟩
      -- shrink a realizer to fit inside U. the conclusion follows by hy.
      sorry
    | inr h_empty =>
      -- choose a U far from the surface. it is always a realizer since theres 1 side
      -- theres one side because any punctured components near p will contain p
      apply not_nonempty_iff.mp at h_empty
      cases Decidable.em (Nonempty {f : F // p ∈ closure f.1.range}) with
      | inl h_closure =>
        have f := (inhabited_of_nonempty h_closure).default
        rcases h_frontier f.1 ⟨p, f.1.1.2.isOpen_range.frontier_eq ▸
          ⟨f.2, fun h ↦ isEmpty_iff.mp h_empty ⟨f.1, h⟩⟩⟩
            with ⟨U, hpU, hU⟩
        -- actually, we need the component of U containing p
        use U, sorry
        intro q hq a b
        rw [hU (q := ⟨q, hq⟩) a b]
        rw [hU (q := ⟨p, hpU⟩) _ _]
      | inr h_closure =>
        apply not_nonempty_iff.mp at h_closure
        -- p is in the complement of the closure of U = ⋃ f:F, f.1.range.
        -- Take the connected component containing p. This is a realizer
        sorry
-/

-- if we have a locally consistent component realizer, then cannonically Homeomorph U MatSpace.
-- for any choice of representative ConnectedComponent of U\S.
-- this is intuitively true because we can reshuffle the components to match material space.


open Classical in theorem composedGluingattern_isLocallyConsistent_iff_of_finite
  [∀ p, Finite (relevant_portal_maps F p)]
  {γ : GluingPattern S (Equiv.Perm F)} (hγ : γ.isLocallyConsistent)
  [∀ p, IsMulCommutative (relevant_perms γ p)]
  [∀ p, TopologicalSpace (relevant_perms γ p)]
  [∀ p, T2Space (relevant_perms γ p)]
  [∀ p, ContinuousMul (relevant_perms γ p)]
  (h_multipliable : ∀ {p : X} (a b : Sides.at_point (union_surface S F) p),
    Multipliable (fun f ↦ relevant_recommendation_map γ f a b) := by assumption)
  (hR : ∀ {p U}, p ∈ U → ∃ (V : Opens X) (R : ComponentRealizer V (union_surface S F) p), V ≤ U)

   -- maybe put this one inside the iff?
  (h_trivial : irrelevants_locally_trivial γ) :

    (composedGluingPattern γ).isLocallyConsistent ↔ irrelevants_locally_trivial γ := by

  have h := composedGluingattern_isLocallyConsistent_iff hγ h_multipliable hR
  apply Iff.intro (And.left <| h.mp ·)
  intro h_trivial
  apply h.mpr
  apply And.intro h_trivial _

  use (choose <| @hγ ·)
  apply And.intro fun _ ↦ choose_spec hγ
  intro p
  apply subset_interior_iff_isOpen.mpr <| isOpen_iInter_of_finite
    (·.1.1.2.isOpen_iff_image_isOpen.mp <| Opens.is_open' _)
  apply Set.mem_iInter.mpr
  intro f
  let p' := f.1.1.inv_range ⟨p, f.2⟩

  use p'
  apply And.intro <| match choose_spec <| @hγ p' with | ⟨R, _⟩ => R.hub_mem


  sorry -- prove this in the portal maps file



end composition_construction





section EqualityConstruction


def recommendations_agree (γ : GluingPattern S (Equiv.Perm F)) {a b : Sides (union_surface S F)}
  (hab : a.center = b.center) (f g : relevant F a.center) : Prop :=
    recommendation_map γ hab f.2 = recommendation_map γ hab g.2


#check Quotient
open Classical in noncomputable def equalityGluingPattern (γ : GluingPattern S (Equiv.Perm F)) :
    GluingPattern (union_surface S F) (Equiv.Perm F) where
  map {a _} hab := if h_nonempty : Nonempty (relevant F a.center) then
    Quot.lift (fun f : relevant F a.center ↦ recommendation_map γ hab f.2) (fun _ _ x ↦ x)
      (@default _ (@Quot.instInhabited_mathlib _ (recommendations_agree γ hab)
        (inhabited_of_nonempty h_nonempty))) else 1
  trans {a _ _} hab hbc := by
    simp?
    -- this seems false
    -- maybe this construction is just wrong

    sorry


end EqualityConstruction



end Portal
