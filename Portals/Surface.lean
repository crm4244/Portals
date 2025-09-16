import MathLib.Topology.Sets.Closeds



variable {X : Type} [hX : TopologicalSpace X]

def Surface (S : Set X) := IsClosed S ∧ interior S = ∅

variable {S : Set X}



namespace Surface

theorem IsClosed (hS : Surface S) : IsClosed S := by
  rcases hS with ⟨h, _⟩
  exact h

theorem interior_eq_empty (hS : Surface S) : interior S = ∅ := by
  rcases hS with ⟨_, h⟩
  exact h

theorem frontier_eq_self (hS : Surface S) : frontier S = S := by
  rcases hS with ⟨hS_closed, hS_int_empty⟩
  unfold frontier
  rw [hS_int_empty]
  rw [Set.diff_empty]
  rw [closure_eq_iff_isClosed]
  exact hS_closed

theorem closure_eq_self (hS : Surface S) : closure S = S :=
  IsClosed.closure_eq (IsClosed hS)


theorem IsOpen_compl (hS : Surface S) : IsOpen Sᶜ := by
  rcases hS with ⟨hS_closed, _⟩
  exact IsClosed.isOpen_compl

theorem IsOpen_sdiff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    IsOpen (U \ S) :=
  IsOpen.sdiff hU (IsClosed hS)

theorem hh (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ closure U ⊆ closure (U \ S) := by
  intro p ⟨hpS, hpU⟩
  rw [em]
  intro V hV hpV


  sorry

end Surface
