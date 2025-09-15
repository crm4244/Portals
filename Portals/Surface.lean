import MathLib.Topology.Connected.Basic



variable {X : Type} [hX : TopologicalSpace X]

def Surface (S : Set X) := IsClosed S ∧ interior S = ∅

variable {S : Set X}



namespace Surface


theorem frontier_eq_self (hS : Surface S) : frontier S = S := by
  rcases hS with ⟨hS_closed, hS_int_empty⟩
  unfold frontier
  rw [hS_int_empty]
  rw [Set.diff_empty]
  rw [closure_eq_iff_isClosed]
  exact hS_closed

theorem IsOpen_compl (hS : Surface S) : IsOpen Sᶜ := by
  rcases hS with ⟨hS_closed, _⟩
  exact IsClosed.isOpen_compl

theorem IsOpen_IsOpen_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    IsOpen (U \ S) := by

  sorry

end Surface
