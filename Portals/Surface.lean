import Mathlib.Topology.Closure
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Constructions

variable {X : Type} [hX : TopologicalSpace X]



def components (A : Set X) : Set (Set X) :=
  {C | ∃ p ∈ A, connectedComponentIn A p = C}

theorem sUnion_components_eq_self (A : Set X) :
    ⋃₀ components A = A := by
  apply Set.eq_of_subset_of_subset
  · exact fun q ⟨_, ⟨_, ⟨_, rfl⟩⟩, hqC⟩ => connectedComponentIn_subset A _ hqC
  · exact (fun q hq => ⟨connectedComponentIn A q,
      by
      unfold components
      simp only [Set.mem_setOf_eq]
      exact ⟨q, ⟨hq, rfl⟩⟩,
    mem_connectedComponentIn hq⟩)

theorem mem_cmpnts_subset {A B : Set X} : A ∈ components B → A ⊆ B := by
  rintro ⟨_, ⟨_, rfl⟩⟩
  exact connectedComponentIn_subset B _




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
theorem inter_closure_subset_cmpnts_closure_finite (hS : Surface S) {U : Set X} (hU : IsOpen U)
    (hUSC_fin : Finite (components (U \ S))) :
    S ∩ closure U ⊆ ⋃ C ∈ components (U \ S), closure C := by
  intro p hpScU
  have hpUS : p ∈ closure (U \ S) := inter_closure_subset_closure_diff hS hU (
    (Set.mem_inter_iff p S (closure U)).mpr hpScU)
  rw [← sUnion_components_eq_self (U \ S), Set.Finite.closure_sUnion hUSC_fin] at hpUS
  exact hpUS

end Surface



theorem maximality {A B C : Set X} (hB : B ∈ components A) (hC : IsPreconnected C) (hCA : C ⊆ A)
    (hCB : (C ∩ B).Nonempty) : C ⊆ B := by
  rcases hCB with ⟨x, hxCB⟩
  rcases hB with ⟨p, ⟨hpA, rfl⟩⟩
  rw [connectedComponentIn_eq hxCB.2]
  exact IsPreconnected.subset_connectedComponentIn hC hxCB.1 hCA



/-
Claim: If the sets A, B have B ⊆ A and C is a connected component of A \ S,
  and K is a connected component of C ∩ B, then K is a connected component of B \ S.

Proof. Since K is a connected subset of C ∩ B = (C \ S) ∩ B = C ∩ (B \ S) ⊆ B \ S,
  we may let H ⊇ K be a connected component of B / S. Note that H and C are
  connected subsets of B / S ⊆ A \ S, and H ∩ C ⊇ K ≠ {}.
  By maximality of C in A \ S, we have H ⊆ C. We also know that H ⊆ B \ S, and so
  H ⊆ C ∩ (B \ S) = (C \ S) ∩ B = C ∩ B. Because K ⊆ H and K is maximal in C ∩ B, H = K.
  Therefore K is a connected component of B \ S.
QED
-/


theorem connectedComponentIn_lemma_1 {A B C K : Set X} (hBA : B ⊆ A) (hC : C ∈ components (A \ S))
    (hK : K ∈ components (C ∩ B)) : K ∈ components (B \ S) := by
  have hCBBS : C ∩ B ⊆ B \ S := fun k hkCB =>
    ⟨hkCB.2, (Set.inter_subset_inter_left B (mem_cmpnts_subset hC) hkCB).1.2⟩
  have hK2 := hK
  rcases hK with ⟨k, ⟨hkCB, rfl⟩⟩
  exact ⟨k, ⟨hCBBS hkCB,
    Set.eq_of_subset_of_subset
      (maximality hK2 isPreconnected_connectedComponentIn
        (Set.subset_inter_iff.mpr ⟨
          maximality hC isPreconnected_connectedComponentIn
            (subset_trans (connectedComponentIn_subset _ k) (Set.diff_subset_diff_left hBA))
            ⟨k, ⟨mem_connectedComponentIn (hCBBS hkCB), hkCB.1⟩⟩,
          subset_trans (connectedComponentIn_subset _ k) Set.diff_subset⟩)
        ⟨k, ⟨mem_connectedComponentIn (hCBBS hkCB), mem_connectedComponentIn hkCB⟩⟩)
      (connectedComponentIn_mono k hCBBS)⟩⟩

/-
  Claim: Let the sets A, B have B ⊆ A.
  Let C1 and C2 be connected components of A \ S and B \ S respectively. Suppose C1 ∩ C2 != {}.
  Then C2 ⊆ C1, and furthermore C2 is a connected component of C1 ∩ B.

  Proof. Note (C1 ∩ B) ∩ C2 = C1 ∩ (B ∩ C2) = C1 ∩ C2 ≠ {}.
  Let x ∈ (C1 ∩ B) ∩ C2 and let K be the connected component of C1 ∩ B which contains x.
  By the first claim, K is a connected component of B \ S.
  Now K and C2 are both connected components of B \ S, and K ∩ C2 ⊇ {x} ≠ {}.
  So, K = C2, and therefore C2 is a connected component of C1 ∩ B, and also C2 ⊆ C1 as desired.

  QED
-/

theorem connectedComponentIn_lemma_2 {A B C D : Set X} (hBA : B ⊆ A) (hCAS : C ∈ components (A \ S))
    (hDBS : D ∈ components (B \ S)) (hCDinter : (C ∩ D).Nonempty) : D ∈ components (C ∩ B) := by
  rcases hCDinter with ⟨p, hpC, hpD⟩
  have hpB := subset_trans (mem_cmpnts_subset hDBS) Set.diff_subset hpD
  have hKBS := connectedComponentIn_lemma_1 hBA hCAS ⟨p, ⟨⟨hpC, hpB⟩, rfl⟩⟩
  have hD : D = connectedComponentIn (B \ S) p := by
    rcases hDBS with ⟨_, _, rfl⟩
    apply connectedComponentIn_eq hpD

  rcases hD
  exact ⟨p, ⟨⟨hpC, hpB⟩, Set.eq_of_subset_of_subset
    (maximality hDBS isPreconnected_connectedComponentIn (mem_cmpnts_subset hKBS)
      ⟨p, mem_connectedComponentIn ⟨hpC, hpB⟩, hpD⟩)
    (maximality hKBS isPreconnected_connectedComponentIn (mem_cmpnts_subset hDBS)
      ⟨p, hpD, mem_connectedComponentIn ⟨hpC, hpB⟩⟩)⟩⟩
