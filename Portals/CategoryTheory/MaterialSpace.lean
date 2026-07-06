
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


theorem center_eq_of_rusto {f : F} (a b : Sides (restrict_union_surface S f))
  (hab : a.center = b.center := by aesop) :
    (restricted_union_side_to_original a).center = (restricted_union_side_to_original b).center :=
  (hab ▸ center_rusto_comm a).trans (center_rusto_comm b).symm


theorem center_eq_of_usto {f : F} (a b : Sides (union_surface S F))
  (hab : a.center = b.center := by aesop) (h_mem : a.center ∈ f.1.opens_range := by aesop) :
    a.restrict_of_mem.center = b.restrict_of_mem.center :=
  Set.injOn_subtype_val (Set.mem_univ _) (Set.mem_univ _)
    (a.restrict_comm.trans <| hab.trans b.restrict_comm.symm)



def recommendation_gluing_pattern (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface S f) (Equiv.Perm F) where
  map a b _ := @γ _ _ (center_eq_of_rusto a b)
  trans a b c _ _ := @γ.trans _ _ _ (center_eq_of_rusto a b) (center_eq_of_rusto b c)

-- might want to check if the recommendation_gluing_pattern is locally consistent. not important yet


noncomputable def recommendation_map (γ : GluingPattern S (Equiv.Perm F))
  (a b : Sides (union_surface S F)) (f : F)
  (hab : a.center = b.center := by aesop) (h_mem : a.center ∈ f.1.opens_range := by aesop) :
    Equiv.Perm F :=
  recommendation_gluing_pattern γ f _ _ (center_eq_of_usto a b)







namespace composition_construction

open TopologicalSpace


def relevant_portal_maps (F : Set (PortalMap Y X)) (p : X) : Sort 1 :=
  { f : F // p ∈ f.1.range }



variable (γ : GluingPattern S (Equiv.Perm F))

def relevantPerms (p : X) : Subgroup (Equiv.Perm F) := Subgroup.closure
  {P : Equiv.Perm F | ∃ (a b : Sides.sides_at (union_surface S F) p) (f : relevant_portal_maps F p),
    recommendation_map γ a.1 b.1 f.1 (a.2.trans b.2.symm) (by rw[a.2]; exact f.2) = P}

def castF (a b : Sides (union_surface S F)) (hab : a.center = b.center := by aesop) :
  relevant_portal_maps F a.center ≃ relevant_portal_maps F b.center := {
    toFun x := ⟨x.1, by rw [← hab]; exact x.2⟩
    invFun x := ⟨x.1, by rw [hab]; exact x.2⟩
  }

def castP (a b : Sides (union_surface S F)) (hab : a.center = b.center := by aesop) :
  relevantPerms γ a.center →* relevantPerms γ b.center := {
    toFun x := ⟨x.1, by rw[hab.symm]; exact x.2⟩
    map_one' := rfl
    map_mul' _ _ := rfl
  }

theorem continuous_castP (a b : Sides (union_surface S F)) (hab : a.center = b.center := by aesop)
  [∀ p, TopologicalSpace (relevantPerms γ p)] : Continuous (castP γ a b) := by
  unfold castP
  simp


  sorry

noncomputable def relevant_recommendation_map
  (from_side to_side map_side perm_side : Sides (union_surface S F))
  (f : relevant_portal_maps F map_side.center)
  (h1 : from_side.center = to_side.center := by aesop)
  (h2 : from_side.center = map_side.center := by aesop)
  (h3 : from_side.center = perm_side.center := by aesop) :
    relevantPerms γ perm_side.center :=
  ⟨recommendation_map γ from_side to_side f.1 h1 (h2.symm ▸ f.2),
    Subgroup.mem_closure_of_mem ⟨⟨from_side, h3⟩, ⟨to_side, h1.symm.trans h3⟩,
    castF map_side perm_side (h2.symm.trans h3) f, rfl⟩⟩




-- we could change the SummationFilter if we want, using unconditional for now

noncomputable def composedGluingPattern (γ : GluingPattern S (Equiv.Perm F))
  [∀ p, IsMulCommutative (relevantPerms γ p)] [∀ p, TopologicalSpace (relevantPerms γ p)]
  [∀ p, T2Space (relevantPerms γ p)] [∀ p, ContinuousMul (relevantPerms γ p)]
  (h_multipliable : ∀ (a b : Sides (union_surface S F)) (hab : a.center = b.center := by aesop),
    Multipliable (relevant_recommendation_map γ a b a a) := by assumption) :
      GluingPattern (union_surface S F) (Equiv.Perm F) where

  map {a b} hab := ↑(∏' f : relevant_portal_maps F a.center,
    relevant_recommendation_map γ a b a a f)
  trans {a b c} hab hbc := by



    rw [← Equiv.tprod_eq (castF a b) (relevant_recommendation_map γ b c b b)]


    have h_mult : Multipliable (relevant_recommendation_map γ b c a b) :=
      let ⟨x, hx⟩ := h_multipliable b c
      ⟨x, ((castF a b).injective.hasProd_iff (by aesop)
        (f := relevant_recommendation_map γ b c b b)).mpr hx⟩



    let x := Multipliable.map_tprod h_mult (castP γ b a) (continuous_castP γ b a)
    let x1 := congr_arg Subtype.val x
    have x_ l : ((castP γ b a) l).1 = l.1 := rfl
    rw [x_ _] at x1
    unfold castP at x1
    unfold castF
    unfold relevant_recommendation_map at x1 ⊢
    simp at ⊢ x1
    rw [x1]

    rw [← Subgroup.coe_mul _ _]
    apply congr_arg
    rw [← Multipliable.tprod_mul (by exact h_multipliable a b)
      (by exact h_mult.map (castP γ b a) (continuous_castP γ b a))]
    apply tprod_congr
    intro f
    unfold recommendation_map
    simp

    exact (recommendation_gluing_pattern γ f.1).trans _ _ _
      (center_eq_of_usto a b hab f.2) (center_eq_of_usto b c hbc (hab ▸ f.2))






theorem composedGluingattern_isLocallyConsistent
  {γ : GluingPattern S (Equiv.Perm F)} (hγ : γ.isLocallyConsistent) :
    (composedGluingPattern γ).isLocallyConsistent := by
      -- change this to "exists a realizing surface so its locally consistent"
      -- use smaller realizers that fit inside the portal maps

  unfold GluingPattern.isLocallyConsistent
  intro p

  unfold GluingPattern.map
  unfold composedGluingPattern
  unfold recommendation_map
  unfold GluingPattern.map
  unfold recommendation_gluing_pattern
  unfold GluingPattern.map
  simp only

  let f : F := sorry
  have hpf : p ∈ f.1.range := sorry
  #check f.1.inv_range ⟨p, hpf⟩
  have hpU' : ↑(f.1.inv_range ⟨p, hpf⟩) ∈ f.1.domain := by
    sorry

  rcases hγ (p := ↑(f.1.inv_range ⟨p, hpf⟩)) with ⟨U, R, _⟩
  #check R.subrealizer hpU'


  sorry
  /-
  q r hrp hrq a b ha hb

  unfold GluingPattern.map
  unfold composedGluingPattern
  unfold recommendation_map
  unfold GluingPattern.map
  unfold recommendation_gluing_pattern
  unfold GluingPattern.map
  simp only



  unfold GluingPattern.isLocallyConsistent at hγ



  #check ComponentRealizer.center_eq_point_of_side_transfer (RU.realizer p) (ha ▸ hrp : a.center ∈ RUf p)
  simp [ComponentRealizer.center_eq_point_of_side_transfer (RU.realizer p) (ha ▸ hrp : a.center ∈ RUf p)]

  --have h := ComponentRealizer.center_eq_point_of_side_transfer (RU.realizer p)
  --  (GluingPattern.isLocallyConsistent._proof_1 RU hrp ha)



  #check tprod

  #check γ.1 (center_eq_of_rusto
    (recommendation_map._proof_2 (composedGluingPattern._proof_1 _)
    (GluingPattern.isLocallyConsistent._proof_2 hrp ha hb)))

  rw [ComponentRealizer.center_eq_point_of_side_transfer ]


  --apply hγ
  #check (hγ sorry sorry sorry sorry : γ.1 _ = γ.1 _)
  #check (hγ (by

    sorry) (by

    sorry) (by

    sorry) (by

    sorry))

  sorry


#check Multipliable
-/





-- if we have a locally consistent component realizer, then cannonically Homeomorph U MatSpace.
-- for any choice of representative ConnectedComponent of U\S.
-- this is intuitively true because we can reshuffle the components to match material space.

end composition_construction




#check isEmpty_iff

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
