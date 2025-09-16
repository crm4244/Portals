
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

theorem IsOpen_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    IsOpen (U \ S) :=
  IsOpen.sdiff hU (IsClosed hS)



theorem hh (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ closure U ⊆ frontier (U \ S) := by
  intro p ⟨hpS, hpU⟩
  unfold frontier
  rw [Set.mem_diff]
  split_ands
  · rw [mem_closure_iff] at hpU ⊢
    intro V hV hpV
    specialize hpU V hV hpV
    rw [← compl_compl S, Set.diff_compl, ← Set.inter_assoc]
    rw [← Set.diff_compl, compl_compl]
    apply Set.nonempty_of_not_subset
    intro hVU
    have hVUi : V ∩ U ⊆ interior S := by
      apply (IsOpen.subset_interior_iff (IsOpen.inter hV hU)).mpr
      exact hVU
    rw [interior_eq_empty hS, Set.subset_empty_iff] at hVUi
    rw [hVUi] at hpU
    exact Set.not_nonempty_empty hpU



  · intro hpUI
    apply interior_subset at hpUI
    rw [Set.mem_diff] at hpUI
    cases hpUI
    contradiction


end Surface


#check mem_closure_iff
