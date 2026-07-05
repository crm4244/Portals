
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


theorem center_eq_of_rusto {f : F} {a b : Sides (restrict_union_surface S f)}
  (hab : a.center = b.center) :
    (restricted_union_side_to_original a).center = (restricted_union_side_to_original b).center :=
  (hab ▸ center_rusto_comm a).trans (center_rusto_comm b).symm




def recommendation_gluing_pattern (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface S f) (Equiv.Perm F) where
  map h := γ (center_eq_of_rusto h)
  trans hab hbc := γ.trans (center_eq_of_rusto hab) (center_eq_of_rusto hbc)

-- might want to check if the recommendation_gluing_pattern is locally consistent. not important yet


noncomputable def recommendation_map (γ : GluingPattern S (Equiv.Perm F))
    {a b : Sides (union_surface S F)} (hab : a.center = b.center)
    {f : F} (h_mem : a.center ∈ f.1.opens_range) : Equiv.Perm F :=
  recommendation_gluing_pattern γ f (Set.injOn_subtype_val (Set.mem_univ _) (Set.mem_univ _)
    ((Sides.restrict_comm h_mem).trans (hab.trans (Sides.restrict_comm (hab ▸ h_mem)).symm)))







namespace composition_construction

open TopologicalSpace


-- here it would suffice to use f.1.range, but using opens_range makes the proofs nicer
def relevant_portal_maps (F : Set (PortalMap Y X)) (p : X) : Sort 1 :=
  { f : F // p ∈ f.1.opens_range }



variable (γ : GluingPattern S (Equiv.Perm F))

def relevantPerms (p : X) : Subgroup (Equiv.Perm F) := Subgroup.closure
  {P : Equiv.Perm F | ∃ (a b : Sides.sides_at (union_surface S F) p) (f : relevant_portal_maps F p),
    recommendation_map γ (a.2.trans b.2.symm) (by rw[a.2]; exact f.2) = P}

def castF {a b : Sides (union_surface S F)} (hab : a.center = b.center) :
  relevant_portal_maps F a.center ≃ relevant_portal_maps F b.center := {
    toFun x := ⟨x.1, by rw [← hab]; exact x.2⟩
    invFun x := ⟨x.1, by rw [hab]; exact x.2⟩
  }

def castP {a b : Sides (union_surface S F)} (hab : a.center = b.center) :
  relevantPerms γ a.center →* relevantPerms γ b.center := {
      toFun x := ⟨x.1, by rw[hab.symm]; exact x.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl
    }

theorem continuous_castP {a b : Sides (union_surface S F)} (hab : a.center = b.center)
  [∀ p, TopologicalSpace (relevantPerms γ p)] : Continuous (castP γ hab) := by
  unfold castP
  simp


  sorry


noncomputable def relevant_recommendation_map {a b c : Sides (union_surface S F)}
  (hab : a.center = b.center) (hbc : b.center = c.center) (f : relevant_portal_maps F a.center) :
    relevantPerms γ c.center :=
  ⟨recommendation_map γ hab f.2, Subgroup.mem_closure_of_mem
    ⟨⟨a, hab.trans hbc⟩, ⟨b, hbc⟩, castF (hab.trans hbc) f, rfl⟩⟩






noncomputable def composedGluingPattern (γ : GluingPattern S (Equiv.Perm F))
  [∀ p, IsMulCommutative (relevantPerms γ p)] [∀ p, TopologicalSpace (relevantPerms γ p)]
  [∀ p, T2Space (relevantPerms γ p)] [∀ p, ContinuousMul (relevantPerms γ p)]
  {h_multipliable : ∀ {a b : Sides (union_surface S F)} (hab : a.center = b.center),
    Multipliable (relevant_recommendation_map γ hab hab.symm)} :
      GluingPattern (union_surface S F) (Equiv.Perm F) where

  map {a b} hab := ↑(∏' f : relevant_portal_maps F a.center, relevant_recommendation_map γ hab hab.symm f)
  trans {a b c} hab hbc := by



    rw [← Equiv.tprod_eq (castF hab) (relevant_recommendation_map γ hbc hbc.symm)]


    let x := Multipliable.map_tprod (sorry : Multipliable (relevant_recommendation_map γ hbc (hbc.symm.trans hab.symm))) (castP γ hab) (continuous_castP γ hab)
    let x1 := congr_arg Subtype.val x
    have x_ l : (castP γ hab l).1 = l.1 := rfl
    rw [x_ _] at x1
    unfold castP at x1
    unfold relevant_recommendation_map at x1 ⊢
    simp at x1


    --have y : castP (relevant_recommendation_map γ hbc sorry) = sorry := sorry
    unfold permAToB relevant_recommendation_map at y
    simp at y


    --have permBToA_map_one : permBToA 1 = 1 := rfl
    --have permBToA_coe_eq (x) : (permBToA x).1 = x.1 := rfl
    --have permBToA_map_mul (x y) : permBToA (x * y) = permBToA x * permBToA y := rfl

    /-
    let castγ : relevantPerms γ a.center ≃ relevantPerms γ b.center := Equiv.cast (hab ▸ rfl)


    have castγ_map_one : castγ 1 = 1 := (Equiv.cast_eq_iff_heq _).mpr
      (Subtype.mk.hcongr_4 _ _ rfl _ _ (hab ▸ HEq.rfl) _ _ HEq.rfl _ _ (hab ▸ HEq.rfl))

    have castγ_coe_eq (x) : (castγ x).1 = x.1 :=
      (Subtype.heq_iff_coe_eq (fun _ ↦ hab ▸ Iff.rfl)).mp (cast_heq _ _)

    have castγ_map_mul (x y) : castγ (x * y) = castγ x * castγ y := Subtype.val_injective
      (Subgroup.coe_mul _ (castγ x) (castγ y) ▸ castγ_coe_eq x ▸ castγ_coe_eq y ▸
        castγ_coe_eq (x * y) ▸ Subgroup.coe_mul _ x y)

    let castγHom : relevantPerms γ a.center →* relevantPerms γ b.center := {
      toFun := castγ
      map_one' := castγ_map_one
      map_mul' := castγ_map_mul
    }

    --#check MulHomClass.mk castγHom
    -/


    /-
    have h_castγ_inj : Function.Injective castγ := fun _ _ ↦ (cast_inj _).mp
    let castγ_inj : relevantPerms γ a.center  relevantPerms γ b.center

    have h_castγ_onehom : castγ 1 = 1 := by
      #check map_eq_one_iff ⟨castγ, h_castγ_inj⟩
      #check (map_eq_one_iff _ _).mpr
      --apply?
      sorry
    -/

    sorry
/-
    have h_bToA : ↑(∏' (f : relevant F a.center), (⟨recommendation_map γ hbc (castf f).2,
      Subgroup.mem_closure_of_mem ⟨⟨b, rfl⟩, ⟨c, hbc.symm⟩, (castf f), rfl⟩⟩ : relevantPerms γ b.center)) =
        @Subtype.val (Equiv.Perm F) _ (∏' (f : relevant F a.center), (⟨recommendation_map γ hbc (castf f).2,
          Subgroup.mem_closure_of_mem ⟨⟨b, hab.symm⟩, ⟨c, hbc.symm.trans hab.symm⟩, f, rfl⟩⟩
        : relevantPerms γ a.center)) := by


      #check Multipliable.map_tprod
      sorry
  -/
      /-
      --simp

      --apply?
      refine (Subtype.heq_iff_coe_eq (by exact?)).mp ?_
      refine (Equiv.cast_eq_iff_heq (by rw[hab])).mp ?_

      apply Multipliable.map_tprod

      refine Eq.symm (Function.Surjective.tprod_eq_tprod_of_hasProd_iff_hasProd ?_ ?_ ?_)
      · exact?
      · sorry
      · intro
        apply?
        sorry

      #check tprod_range
      have h2 := Equiv.tprod_eq
        (Equiv.cast (hab ▸ rfl) : relevant F a.center ≃ relevant F b.center)
        (fun f ↦ recommendation_map γ hbc f.2)

      rw [← h2]
      apply tprod_congr
      intro f
      congr
      exact hab ▸ rfl
      exact cast_heq (hab ▸ rfl) f
    #check CommMonoid.ofIsMulCommutative
    #check IsMulCommutative
    rw [h]
    #check Multipliable.tprod_mul (β := relevant F a.center) (f := fun f ↦ recommendation_map γ hab f.2) _
    --rw [← Multipliable.tprod_mul _ _]
    sorry

-/


/-
    --#check fun (f : F) ↦ f a
    #check Multipliable.tprod_mul _ _
    --unfold recommendation_map
    have habf := fun (f : relevant F a.center) ↦ recommendation_map._proof_2 f.property hab
    have hbcf := fun (f : relevant F a.center) ↦ recommendation_map._proof_2 (hcast f).property hbc
    #check (habf : ∀ f, (Sides.restrict_of_mem (_ : a.center ∈ _)).center =
      (Sides.restrict_of_mem (_ : b.center ∈ _)).center)
    #check hbcf
    #check fun (f : relevant F a.center) ↦ recommendation_map._proof_2 f.property (Eq.trans hab hbc)
    --rw [← (recommendation_gluing_pattern γ _).trans]
    #check (recommendation_gluing_pattern γ _).trans _ _

    have h_cast_eq (f : relevant F a.center) : f.1 = (hcast f).1 := by
      unfold hcast
      #check (Equiv.cast_eq_iff_heq (hab ▸ rfl : ↑(relevant F a.center) = ↑(relevant F b.center))).mpr
      --unfold relevant
      apply Subtype.coe_eq_iff.mpr
      have h : a.center ∈ (hcast f).1.1.opens_range := by
        rw [hab]
        exact (hcast f).2
      #check hcast f
      use h

      sorry

    have h_trans (f : relevant F a.center) := (recommendation_gluing_pattern γ f.1).trans
      (habf f) (hbcf f)
    --#check h_trans

    --classical
    unfold recommendation_map
    simp only

    --sorry
    #check Subtype.coe_eq_iff

    --unfold recommendation_map
    --#check
    #check ((recommendation_gluing_pattern γ _).trans _ _).symm


    --rw [← γ.trans]
    sorry
-/

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
