import Portals.Basic



variable {X : Type} [hX : TopologicalSpace X]

class Surface (S : Set X) where
  isClosed : IsClosed S
  interior_eq_empty : interior S = ∅

variable {S : Set X}





namespace Surface



theorem frontier_eq_self (hS : Surface S) : frontier S = S := by
  rw [frontier, hS.interior_eq_empty, Set.diff_empty]
  exact closure_eq_iff_isClosed.mpr hS.1

theorem closure_eq_self (hS : Surface S) : closure S = S :=
  IsClosed.closure_eq (hS.isClosed)

/-
theorem IsOpen_compl (hS : Surface S) : IsOpen Sᶜ := isOpen_compl_iff.mpr hS.1

theorem IsOpen_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) : IsOpen (U \ S) :=
  IsOpen.sdiff hU (IsClosed hS)
-/

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
    rw [hS.interior_eq_empty] at hVUi
    exact Set.nonempty_iff_ne_empty.mp
      (mem_closure_iff.mp hpU V hV hpV)
      (Set.subset_empty_iff.mp hVUi)
  · exact fun h => ((Set.mem_diff p).mp (interior_subset h)).2 hpS


theorem inter_closure_subset_closure_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ closure U ⊆ closure (U \ S) := fun p ⟨hpS, hpU⟩ =>
  frontier_subset_closure (
    inter_closure_subset_frontier_diff hS hU (
      (Set.mem_inter_iff p S (closure U)).mpr ⟨hpS, hpU⟩))


theorem inter_subset_closure_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ U ⊆ closure (U \ S) := fun p ⟨hpS, hpU⟩ =>
  frontier_subset_closure (
    inter_closure_subset_frontier_diff hS hU (
      (Set.mem_inter_iff p S (closure U)).mpr ⟨hpS, subset_closure hpU⟩))


/-
  Let U be an open set and p ∈ S have p ∈ cl(U).
  Suppose U / S has finitely many connected components.
  Then there is a connected component C of U \ S with p ∈ cl(C).
-/
theorem inter_closure_subset_cmpnts_closure (hS : Surface S) {U : Set X} (hU : IsOpen U)
    (hUSC_fin : Finite (components (U \ S))) :
    S ∩ closure U ⊆ ⋃ C ∈ components (U \ S), closure C := by
  intro p hpScU
  have hpUS : p ∈ closure (U \ S) := inter_closure_subset_closure_diff hS hU (
    (Set.mem_inter_iff p S (closure U)).mpr hpScU)
  rw [← sUnion_cmpnts (U \ S), Set.Finite.closure_sUnion hUSC_fin] at hpUS
  exact hpUS



end Surface
