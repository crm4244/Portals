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




def Side (S : Set X) := Quotient (Setoid.mk (ESide.touches S) (ESide.Equivalence S))



namespace Side


noncomputable def center (S : Set X) (a : Side S) : X :=
  Quotient.liftOn a (IsESide.center ·.2) (IsESide.center_eq_of_touches ·.2 ·.2 ·)


def stouches (S : Set X) (a : Side S) (A : Set X) : Prop :=
  Quotient.liftOn a (IsESide.stouches ·.1 ·)
    (fun e1 e2 he ↦ funext fun _ ↦ eq_iff_iff.mpr (Iff.intro
        (IsESide.stouches_of_touches_of_stouches e1.2 e2.2 he ·)
        (IsESide.stouches_of_touches_of_stouches e2.2 e1.2
          ((ESide.Equivalence S).symm he) ·)))
  A


--def wtouches (S : Set X) (a : Side S) (A : Set X) : Prop :=
-- needs a theorem from the IsESide file: "IsESide.wtouches_of_touches_of_wtouches"


end Side



def SideSpace (S : Set X) : TopologicalSpace (Side S) :=
  TopologicalSpace.generateFrom {{a : Side S | Side.stouches S a (e.1 n)} | (n : ℕ) (e : ESide S)}


-- center is continuous
-- center, restricted to a A : Set X where Disjoint A S, is homeomorphic on its image
-- SideSpace is a T2Space
