import Portals.ESide


variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X]


def ESides (S : Set X) := {a : ℕ → Set X | ESide S a}
def ESides_touch (S : Set X) : (ESides S) → (ESides S) → Prop :=
  fun ⟨a, _⟩ ⟨b, _⟩ => ESide.touches a b

def isEquivalence_ESides_touch (S : Set X) : Equivalence (ESides_touch S) := Equivalence.mk
    (fun ⟨_, ha⟩ => ESide.touches_refl ha)
    (fun hab => ESide.touches_symm hab)
    (@fun ⟨_, ha⟩ ⟨_, hb⟩ ⟨_, hc⟩ hab hbc => ESide.touches_trans ha hb hc hab hbc)


def ESide_Setoid (S : Set X) := Setoid.mk (ESides_touch S) (isEquivalence_ESides_touch S)

/-
def ESideSpace (S : Set X) : TopologicalSpace (ESides S) := TopologicalSpace.generateFrom
  {{b' : ESides S | ESide.stouches (b' : ℕ → Set X) ((a' : ℕ → Set X) n)} | (n : ℕ) (a' : ESides S)}
-/


#check fun S => (fun a => Quotient.mk (ESide_Setoid S) a)

def Sides (S : Set X) : ESides S → Quotient (ESide_Setoid S) := sorry




def SideSpace (S : Set X) : TopologicalSpace (Sides S) := TopologicalSpace.generateFrom
  sorry



#check Setoid.mk
