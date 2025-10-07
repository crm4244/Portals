import Portals.IsESide
import Mathlib.Topology.Bases


variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X]


def ESide (S : Set X) : Type := { e : ℕ → Set X // IsESide S e }

def ESide.touches (S : Set X) : ESide S → ESide S → Prop :=
  fun ⟨a, _⟩ ⟨b, _⟩ => IsESide.touches a b

def ESide.Equivalence (S : Set X) : Equivalence (ESide.touches S) := Equivalence.mk
  (IsESide.touches_refl ·.2)
  IsESide.touches_symm
  (@fun ⟨_, ha⟩ ⟨_, hb⟩ ⟨_, hc⟩ hab hbc => IsESide.touches_trans ha hb hc hab hbc)




def Side (S : Set X) : Type := Quotient (Setoid.mk (ESide.touches S) (ESide.Equivalence S))



namespace Side


def stouches {S : Set X} (a : Side S) (A : Set X) : Prop :=
  Quotient.liftOn a (IsESide.stouches ·.1 ·)
    (fun e1 e2 he ↦ funext fun _ ↦ eq_iff_iff.mpr (Iff.intro
        (IsESide.stouches_of_touches_of_stouches e1.2 e2.2 he ·)
        (IsESide.stouches_of_touches_of_stouches e2.2 e1.2
          ((ESide.Equivalence S).symm he) ·)))
  A


--def wtouches (S : Set X) (a : Side S) (A : Set X) : Prop :=
-- needs a theorem from the IsESide file: "IsESide.wtouches_of_touches_of_wtouches"



def instTopologicalSpace (S : Set X) : TopologicalSpace (Side S) :=
  TopologicalSpace.generateFrom {{a : Side S | Side.stouches a (e.1 n)} | (n : ℕ) (e : ESide S)}


instance hSideSpace (S : Set X) : TopologicalSpace (Side S) := instTopologicalSpace S


noncomputable def center {S : Set X} (a : Side S) : X :=
  Quotient.liftOn a (IsESide.center ·.2) (IsESide.center_eq_of_touches ·.2 ·.2 ·)



-- comoponent realizing neighborhoods, existence and uniqueness
theorem exists_mem_cmpnts_diff_surface_stouches_of_center_mem_IsOpen {S : Set X} (a : Side S)
  {A : Set X} (hA : IsOpen A) (hcA : center a ∈ A) :
    ∃ C ∈ components (A \ S), stouches a C := sorry


theorem unique_mem_cmpnts_diff_surface_stouches_of_center_mem_IsOpen {S : Set X} (a : Side S)
    {A B C : Set X} (hA : IsOpen A) (hcA : center a ∈ A)
    (hBAS : B ∈ components (A \ S)) (hBa : stouches a B)
    (hCAS : C ∈ components (A \ S)) (hCa : stouches a C) : B = C := sorry


def toComponent {S : Set X} (a : Side S) {A : Set X} (hA : IsOpen A) (hcA : center a ∈ A) : Set X :=
  Classical.choose (exists_mem_cmpnts_diff_surface_stouches_of_center_mem_IsOpen a hA hcA)


theorem toComponent_component {S : Set X} (a : Side S) {A : Set X} (hA : IsOpen A)
  (hcA : center a ∈ A) : toComponent a hA hcA ∈ components (A \ S) := sorry


theorem toComponent_unique {S : Set X} (a : Side S) {A B : Set X} (hA : IsOpen A)
  (hcA : center a ∈ A) (hBAS : B ∈ components (A \ S)) (hBa : stouches a B) :
  B = toComponent a hA hcA := sorry


theorem center_continuous (S : Set X) : Continuous (@center _ _ _ S) := sorry


noncomputable def center_nmem_homeomorph_of_surjective (S : Set X)
  (hSurj : Function.Surjective (@center _ _ _ S)) :
    Homeomorph (Subtype ((@center _ _ _ S)⁻¹' Sᶜ)) (Subtype Sᶜ) :=
  have hCenterUnique {p : X} (hp : p ∈ Sᶜ) {a b : Side S}
    (ha : a.center = p) (hb : b.center = p) : a = b := sorry
  let eq : Equiv (Subtype ((@center _ _ _ S)⁻¹' Sᶜ)) (Subtype Sᶜ) := Equiv.mk
    (fun a => ⟨center a.1, a.2⟩)
    (fun p => ⟨Classical.choose (hSurj p), fun h => (Classical.choose_spec (hSurj p) ▸ p.2) h⟩)
    (fun ⟨a, ha⟩ => by
      simp only [Subtype.mk.injEq]
      exact hCenterUnique ha (Classical.choose_spec (hSurj a.center)) rfl
    )
    (fun ⟨p, _⟩ => by
      simp only [Subtype.mk.injEq]
      exact Classical.choose_spec (hSurj p)
    )

  by
  apply Homeomorph.mk eq _ sorry
  -- #check Continuous.restrict (Set.MapsTo.restrict eq.toFun sorry sorry sorry)
  sorry


theorem T2Space_SideSpace (S : Set X) : T2Space (Side S) := sorry



end Side
