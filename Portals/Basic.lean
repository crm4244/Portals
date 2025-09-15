


import MathLib.Topology.Basic
import MathLib.Topology.Connected.Basic
/-import MathLib.Topology.Compactness.LocallyCompact-/
import MathLib.Topology.Separation.Hausdorff


variable {X : Type} [hX1 : TopologicalSpace X] [hX2 : Hausdorff X] [hX3 : LocallyCompact X]

def Surface (S : Set X) := IsClosed S ∧ IsEmpty (Interior S)





def ESide (a : ℕ → Set X) :=
  ∃ E, (
    Encapsulation E ∧
    (∀ n, ∃ q, q ∈ E n ∧ a n = connectedComponent q) ∧
    (∀ n, a (n + 1) ⊆ a n)
  )



lemma ESide_center_exists (a : ℕ → Set X) : ESide a → ∃ c, c ∈ (⋂ n, closure (a n)) := sorry



lemma ESide_center_unique (a : ℕ → Set X) : ESide a →
  ∀ c d, (c ∈ ⋂ n, closure (a n) ∧ d ∈ ⋂ n, closure (a n) → c=d) := sorry



  /-
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  Cantor's Intersection Theorem
  -/
