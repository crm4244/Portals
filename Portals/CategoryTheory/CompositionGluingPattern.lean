import Portals.CategoryTheory.Recommendations




namespace Portal


variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {S : Set Y}
variable {F : Set (PortalMap Y X)}


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



open TopologicalSpace


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




end Portal
