
import Portals.CategoryTheory.Realizers



variable {X : Type} [TopologicalSpace X]


namespace Portal

open ComponentRealizer




class GluingPattern (S : Set X) (G : Type) [Group G] where
  map {a b : Sides S} : a.center = b.center → G
  trans {a b c : Sides S} (hab : a.center = b.center) (hbc : b.center = c.center) :
    map hbc * map hab = map (Eq.trans hab hbc)


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
    {a b : Sides S} (hab : a.center = b.center) : γ hab * γ (Eq.symm hab) = 1 :=
  γ.trans (Eq.symm hab) hab ▸ refl_id γ b


omit [TopologicalSpace X] in theorem symm_inv_left (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ (Eq.symm hab) * γ hab = 1 :=
  γ.trans hab (Eq.symm hab) ▸ refl_id γ a


-- a convinent alias for the side_transfer function
def _t [R : RealizingSurface S] {p r : X} (hrp : r ∈ (R.realizer p).set)
    {σ : Sides S} (hσ : σ.center = r) : { a // Sides.center S a = p } :=
  side_transfer (R.realizer p) (hσ ▸ hrp)


def isLocallyConsistent [R : RealizingSurface S] (γ : GluingPattern S G) : Prop :=
  ∀ {p q r : X}, (hrp : r ∈ (R.realizer p).set) → (hrq : r ∈ (R.realizer q).set) →
  ∀ {a b : Sides S}, (ha : a.center = r) → (hb : b.center = r) →
  γ (by rw [(_t hrp ha).2, (_t hrp hb).2] : (_t hrp ha).1.center = (_t hrp hb).1.center) =
  γ (by rw [(_t hrq ha).2, (_t hrq hb).2] : (_t hrq ha).1.center = (_t hrq hb).1.center)


end GluingPattern




end Portal
