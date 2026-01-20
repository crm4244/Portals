
import Mathlib.Algebra.Group.End
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
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
  (hab ▸ center_rusto_comm a).trans (center_rusto_comm b).symm




def recommendation_gluing_pattern (γ : GluingPattern S (Equiv.Perm F)) (f : F) :
    GluingPattern (restrict_union_surface f) (Equiv.Perm F) where
  map := fun x ↦ γ (center_eq_of_rusto x.2)
  trans hab hbc := γ.trans (center_eq_of_rusto hab) (center_eq_of_rusto hbc)

-- might want to check if the recommendation_gluing_pattern is locally consistent. not important yet


noncomputable def recommendation_map (γ : GluingPattern S (Equiv.Perm F))
  {f : F} {a b : Sides (union_surface F)}
    (h_mem : a.center ∈ f.1.opens_range) (hab : a.center = b.center) :
    Equiv.Perm F :=
  recommendation_gluing_pattern γ f (Set.injOn_subtype_val (Set.mem_univ _) (Set.mem_univ _)
    ((Sides.restrict_comm h_mem).trans (hab.trans (Sides.restrict_comm (hab ▸ h_mem)).symm)))







namespace composition_construction

open TopologicalSpace

variable [TopologicalSpace (Equiv.Perm F)]
variable [CommMonoid (Equiv.Perm F)] -- this is a really strict condition

variable (Rf : X → Opens X) (R : RealizingSurface S Rf)
variable (RUf : X → Opens X) (RU : RealizingSurface (union_surface F) RUf)



-- here it would suffice to use f.1.range, but using opens_range makes the proofs nicer
def relevant (F : Set (PortalMap S)) (p : X) : Sort 1 := { f : F // p ∈ f.1.opens_range }


noncomputable def composedGluingPattern (γ : GluingPattern S (Equiv.Perm F)) :
    GluingPattern (union_surface F) (Equiv.Perm F) where
  map x := ∏' f : relevant F x.1.1.center, (recommendation_map γ f.2 x.2)
  trans := by
    intro a b c hab hbc
    let hcast : ↑(relevant F a.center) → ↑(relevant F b.center) :=
      cast (hab ▸ rfl : ↑(relevant F a.center) = ↑(relevant F b.center))
    --rw [← Equiv.tprod_eq hatob _]
    unfold recommendation_map
    simp only

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

theorem composedGluingattern_isLocallyConsistent
  {γ : GluingPattern S (Equiv.Perm F)} (hγ : γ.isLocallyConsistent R) :
    (composedGluingPattern γ).isLocallyConsistent RU := by
      -- change this to "exists a realizing surface so its locally consistent"
      -- use smaller realizers that fit inside the portal maps

  --unfold GluingPattern.isLocallyConsistent
  intro p q r hrp hrq a b ha hb

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

end composition_construction






section EqualityConstruction


def recommendations_agree (γ : GluingPattern S (Equiv.Perm F)) :
-- use the intersection f.1.1.domain ∩ g.1.1.domain
    ∀ (p : X) (f g : { x : F | p ∈ x.1.range }), recommendation γ f = recommendation γ g :=
  sorry


end EqualityConstruction



end Portal
