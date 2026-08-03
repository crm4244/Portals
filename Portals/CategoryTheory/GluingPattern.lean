
import Portals.CategoryTheory.Realizers


universe u v



variable {X : Type u}


namespace Portal

open ComponentRealizer



class GluingPattern (S : Set X) (G : Type v) [Group G] where
  map {p : X} (a b : Sides.at_point S p) : G
  trans {p : X} (a b c : Sides.at_point S p) :
      map a b * map b c = map a c


instance (S : Set X) (G : Type v) [Group G] : CoeFun (GluingPattern S G)
  (fun _ ↦ {p : X} → (a b : Sides.at_point S p) → G) :=
    {coe γ := @γ.map}



namespace GluingPattern

variable {S : Set X} {G : Type v} [Group G] (γ : GluingPattern S G)


def is_trivial_at (p : X) : Prop := ∀ (a b : Sides.at_point S p), γ a b = 1
def is_trivial_on (A : Set X) := ∀ {p : A}, γ.is_trivial_at p
def is_trivial : Prop := γ.is_trivial_on ⊤


theorem refl_id
  {p : X} (a : Sides.at_point S p) :
    γ a a = 1 := by
  have h := γ.trans a a a
  nth_rw 3 [← mul_one (γ a a)] at h
  exact mul_left_cancel h


in theorem symm_inv_right
    {p : X} (a b : Sides.at_point S p) : γ a b * γ b a = 1 :=
  (γ.trans a b a).trans (refl_id γ a)


in theorem symm_inv_left
        {p : X} (a b : Sides.at_point S p) : γ b a * γ a b = 1 :=
  (γ.trans b a b).trans (refl_id γ b)



open TopologicalSpace


variable [TopologicalSpace X]

def respects_realizer {U p} (R : ComponentRealizer U S p) : Prop :=
  ∀ {q : U} (a b : Sides.at_point S q),
    γ (R.side_transfer_at a) (R.side_transfer_at b) = γ a b


def isLocallyConsistent : Prop :=
  ∀ {p : X}, ∃ (U : Opens X) (R : ComponentRealizer U S p), γ.respects_realizer R

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
