
import Mathlib.Topology.Basic
import Portals.Encapsulation


variable {X : Type}


def ESide (a : ℕ → Set X) :=
  ∃ E, (
    Encapsulation E ∧
    (∀ n, ∃ q, q ∈ E n ∧ a n = connectedComponent q) ∧
    (∀ n, a (n + 1) ⊆ a n)
  )



theorem ESide_center_exists (a : ℕ → Set X) : ESide a → ∃ c, c ∈ (⋂ n, closure (a n)) := sorry



theorem ESide_center_unique (a : ℕ → Set X) : ESide a →
  ∀ c d, (c ∈ ⋂ n, closure (a n) ∧ d ∈ ⋂ n, closure (a n) → c=d) := sorry
