
import Portals.CategoryTheory.Realizers



variable {X : Type} [TopologicalSpace X]


namespace Portal

open ComponentRealizer



class GluingPattern (S : Set X) (G : Type) [Group G] where
  map (a b : Sides S) (hab : a.center = b.center := by aesop) : G
  trans (a b c : Sides S)
    (hab : a.center = b.center := by aesop)
    (hbc : b.center = c.center := by aesop) :
      map a b * map b c = map a c


instance (S : Set X) (G : Type) [Group G] : CoeFun (GluingPattern S G)
  (fun _ ↦ (a b : Sides S) → (a.center = b.center) → G) :=
    {coe γ := @γ.map}



namespace GluingPattern

variable {S : Set X} {G : Type} [Group G]



omit [TopologicalSpace X] in theorem refl_id (γ : GluingPattern S G) (a : Sides S) :
    γ a a = 1 := by
  have h := γ.trans a a a
  nth_rw 3 [← mul_one (γ a a)] at h
  exact mul_left_cancel h


omit [TopologicalSpace X] in theorem symm_inv_right (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ a b * γ b a = 1 :=
  (γ.trans a b a).trans (refl_id γ a)


omit [TopologicalSpace X] in theorem symm_inv_left (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ b a * γ a b = 1 :=
  (γ.trans b a b).trans (refl_id γ b)


open TopologicalSpace



def isLocallyConsistent (γ : GluingPattern S G) : Prop :=
  ∀ {p : X}, ∃ (U : Opens X) (R : ComponentRealizer U S p),
  ∀ (q : X) (hq : q ∈ U) {a b : Sides S}
    (ha : a.center = q := by aesop) (hb : b.center = q := by aesop),
  @γ (R.side_transfer a) (R.side_transfer b)
    ((R.center_eq_hub_of_side_transfer a).trans (R.center_eq_hub_of_side_transfer b).symm)
  = γ a b

/- TODO: update this to not use RealizingSurface
def isLocallyConsistent' (γ : GluingPattern S G) : Prop :=
  ∀ {p q r : X}, (hrp : r ∈ f p) → (hrq : r ∈ f q) →
  ∀ {a b : Sides S}, (ha : a.center = r) → (hb : b.center = r) →
    γ ((_t R hrp ha).trans (_t R hrp hb).symm) = γ ((_t R hrq ha).trans (_t R hrq hb).symm)



-- now that ive proved this, we can rethink the defninitions a bit
theorem isLocallyConsistent'_of_isLocallyConsistent (γ : GluingPattern S G)
  {f : X → Opens X} (R : RealizingSurface S f) :
    isLocallyConsistent γ R → isLocallyConsistent' γ R :=
  fun h _ _ _ hrp hrq _ _ ha hb ↦ (h hrp ha hb).trans (h hrq ha hb).symm
-/

end GluingPattern




end Portal
