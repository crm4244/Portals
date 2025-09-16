
import MathLib.Topology.Sets.Closeds



variable {X : Type} [hX : TopologicalSpace X]

def Surface (S : Set X) := IsClosed S ∧ interior S = ∅

variable {S : Set X}



namespace Surface


theorem IsClosed (hS : Surface S) : IsClosed S := hS.1

theorem interior_eq_empty (hS : Surface S) : interior S = ∅ := hS.2

theorem frontier_eq_self (hS : Surface S) : frontier S = S := by
  rw [frontier, hS.2, Set.diff_empty]
  exact closure_eq_iff_isClosed.mpr hS.1

theorem closure_eq_self (hS : Surface S) : closure S = S :=
  IsClosed.closure_eq (IsClosed hS)


theorem IsOpen_compl (hS : Surface S) : IsOpen Sᶜ := isOpen_compl_iff.mpr hS.1

theorem IsOpen_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) : IsOpen (U \ S) :=
  IsOpen.sdiff hU (IsClosed hS)



theorem inter_closure_subset_frontier_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ closure U ⊆ frontier (U \ S) := by
  intro p ⟨hpS, hpU⟩
  unfold frontier
  rw [Set.mem_diff]
  split_ands
  · apply mem_closure_iff.mpr
    intro V hV hpV
    rw [← compl_compl S, Set.diff_compl, ← Set.inter_assoc]
    rw [← Set.diff_compl, compl_compl]
    apply Set.nonempty_of_not_subset
    intro hVU
    have hVUi := (IsOpen.subset_interior_iff (IsOpen.inter hV hU)).mpr hVU
    rw [interior_eq_empty hS] at hVUi
    exact Set.nonempty_iff_ne_empty.mp
      (mem_closure_iff.mp hpU V hV hpV)
      (Set.subset_empty_iff.mp hVUi)
  · exact fun h => ((Set.mem_diff p).mp (interior_subset h)).2 hpS



end Surface
