
import Portals.CategoryTheory.Realizers



variable {X : Type} [TopologicalSpace X]


namespace Portal

open ComponentRealizer



class GluingPattern (S : Set X) (G : Type) [Group G] where
  map : { (a, b) : Sides S × Sides S | a.center = b.center } → G
  trans {a b c : Sides S} (hab : a.center = b.center) (hbc : b.center = c.center) :
    map ⟨(a, b), hab⟩ * map ⟨(b, c), hbc⟩ = map ⟨(a, c), hab.trans hbc⟩


instance (S : Set X) (G : Type) [Group G] : CoeFun (GluingPattern S G)
    (fun _ ↦ {a b : Sides S} → a.center = b.center → G) :=
  {coe γ := (fun {a b : Sides S} (h : a.center = b.center) ↦ γ.map ⟨(a, b), h⟩)}



namespace GluingPattern

variable {S : Set X} {G : Type} [Group G]


omit [TopologicalSpace X] in theorem refl_id (γ : GluingPattern S G) (a : Sides S) :
    γ (Eq.refl a.center) = 1 := by
  have h := γ.trans (Eq.refl a.center) (Eq.refl a.center)
  nth_rw 3 [← mul_one (γ.map ⟨(a, a), rfl⟩)] at h
  exact mul_left_cancel h


omit [TopologicalSpace X] in theorem symm_inv_right (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ hab * γ hab.symm = 1 :=
  (γ.trans hab hab.symm).trans (refl_id γ a)


omit [TopologicalSpace X] in theorem symm_inv_left (γ : GluingPattern S G)
    {a b : Sides S} (hab : a.center = b.center) : γ hab.symm * γ hab = 1 :=
  (γ.trans hab.symm hab).trans (refl_id γ b)


open TopologicalSpace

-- a convinent little version of the side_transfer function
noncomputable def _t {f : X → Opens X} (R : RealizingSurface S f) {p r : X} (hrp : r ∈ f p)
  {σ : Sides S} (hσ : σ.center = r) :
    ((R.realizer p).side_transfer (hσ ▸ hrp)).center = p :=
  (R.realizer p).center_eq_hub_of_side_transfer (hσ ▸ hrp)


def isLocallyConsistent (γ : GluingPattern S G)
    {f : X → Opens X} (R : RealizingSurface S f) : Prop :=
  ∀ {p q : X}, (h : q ∈ f p) →
  ∀ {a b : Sides S}, (ha : a.center = q) → (hb : b.center = q) →
    γ ((_t R h ha).trans (_t R h hb).symm) = γ (ha.trans hb.symm)


def isLocallyConsistent' (γ : GluingPattern S G)
    {f : X → Opens X} (R : RealizingSurface S f) : Prop :=
  ∀ {p q r : X}, (hrp : r ∈ f p) → (hrq : r ∈ f q) →
  ∀ {a b : Sides S}, (ha : a.center = r) → (hb : b.center = r) →
    γ ((_t R hrp ha).trans (_t R hrp hb).symm) = γ ((_t R hrq ha).trans (_t R hrq hb).symm)



-- now that ive proved this, we can rethink the defninitions a bit
theorem isLocallyConsistent'_of_isLocallyConsistent (γ : GluingPattern S G)
  {f : X → Opens X} (R : RealizingSurface S f) :
    isLocallyConsistent γ R → isLocallyConsistent' γ R :=
  fun h _ _ _ hrp hrq _ _ ha hb ↦ (h hrp ha hb).trans (h hrq ha hb).symm

end GluingPattern




end Portal
