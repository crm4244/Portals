
import Portals.CategoryTheory.Realizers



variable {X : Type} [TopologicalSpace X]


namespace Portal

open ComponentRealizer




class GluingPattern (S : Set X) (G : Type) [Group G] where
  map {a b : Sides S} : a.center = b.center → G
  trans {a b c : Sides S} (hab : a.center = b.center) (hbc : b.center = c.center) :
    map hbc * map hab = map (hab.trans hbc)


instance (S : Set X) (G : Type) [Group G] : CoeFun (GluingPattern S G)
  (fun _ ↦ {a b : Sides S} → a.center = b.center → G) := {coe γ := γ.map}



namespace GluingPattern

variable {S : Set X} {G : Type} [Group G]


omit [TopologicalSpace X] in theorem refl_id (γ : GluingPattern S G) (a : Sides S) :
    γ (Eq.refl a.center) = 1 := by
  have ha := Eq.refl a.center
  have h := γ.trans ha ha
  nth_rw 3 [← mul_one (γ.map ha)] at h
  exact mul_left_cancel h


omit [TopologicalSpace X] in theorem symm_inv_right (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ hab * γ hab.symm = 1 :=
  γ.trans hab.symm hab ▸ refl_id γ b


omit [TopologicalSpace X] in theorem symm_inv_left (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ hab.symm * γ hab = 1 :=
  γ.trans hab hab.symm ▸ refl_id γ a


-- a convinent little version of the side_transfer function
noncomputable def _t [R : RealizingSurface S] {p r : X} (hrp : r ∈ (R.realizer p).domain)
  {σ : Sides S} (hσ : σ.center = r) :
    ((R.realizer p).side_transfer (hσ ▸ hrp)).center = p :=
  (R.realizer p).center_eq_point_of_side_transfer (hσ ▸ hrp)


def isLocallyConsistent [R : RealizingSurface S] (γ : GluingPattern S G) : Prop :=
  ∀ {p q r : X}, (hrp : r ∈ (R.realizer p).domain) → (hrq : r ∈ (R.realizer q).domain) →
  ∀ {a b : Sides S}, (ha : a.center = r) → (hb : b.center = r) →
    γ ((_t hrp ha).trans (_t hrp hb).symm) = γ ((_t hrq ha).trans (_t hrq hb).symm)


end GluingPattern




end Portal
