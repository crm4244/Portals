import Mathlib.Topology.Connected.Basic



variable {X : Type} [hX : TopologicalSpace X]


def components (A : Set X) : Set (Set X) :=
  {C | ∃ p ∈ A, connectedComponentIn A p = C}




theorem connectedComponentIn_mem_cmpnts {A : Set X} {p : X} (hpA : p ∈ A) :
    connectedComponentIn A p ∈ components A := ⟨p, ⟨hpA, rfl⟩⟩


theorem sUnion_cmpnts (A : Set X) : ⋃₀ components A = A := by
  apply Set.eq_of_subset_of_subset
  · exact fun q ⟨_, ⟨_, ⟨_, rfl⟩⟩, hqC⟩ ↦ connectedComponentIn_subset A _ hqC
  · exact (fun q hq ↦ ⟨connectedComponentIn A q,
      connectedComponentIn_mem_cmpnts hq, mem_connectedComponentIn hq⟩)


theorem mem_cmpnts_subset {A B : Set X} : A ∈ components B → A ⊆ B :=
  fun ⟨_, ⟨_, h⟩⟩ ↦ h ▸ connectedComponentIn_subset B _


theorem mem_cmpnts_nonempty {A B : Set X} : A ∈ components B → A.Nonempty :=
  fun h ↦ match h with | ⟨p, hp⟩ => ⟨p, (hp.2) ▸ (mem_connectedComponentIn hp.1)⟩


theorem isPreconnected_mem_cmpnts {A B : Set X} (hAB : A ∈ components B) : IsPreconnected A :=
  match hAB with | ⟨_, hp⟩ => hp.2 ▸ isPreconnected_connectedComponentIn


theorem isConnected_mem_cmpnts {A B : Set X} (hAB : A ∈ components B) : IsConnected A :=
  ⟨mem_cmpnts_nonempty hAB, isPreconnected_mem_cmpnts hAB⟩


theorem mem_cmpnts_maximal {A B C : Set X} (hB : B ∈ components A)
    (hC : IsPreconnected C) (hCA : C ⊆ A) (hCB : (C ∩ B).Nonempty) : C ⊆ B := by
  rcases hCB with ⟨x, hxCB⟩
  rcases hB with ⟨p, ⟨hpA, rfl⟩⟩
  rw [connectedComponentIn_eq hxCB.2]
  exact IsPreconnected.subset_connectedComponentIn hC hxCB.1 hCA


theorem exists_subset_mem_cmpnts_of_subset {A B : Set X} (hBA : B ⊆ A)
    (hB : IsConnected B) : ∃ C ∈ components A, B ⊆ C :=
  match hB.1 with
  | ⟨p, hpB⟩ =>
    have hpA := hBA hpB
    have hpA2 := connectedComponentIn_mem_cmpnts hpA
    ⟨connectedComponentIn A p, ⟨hpA2, mem_cmpnts_maximal hpA2 hB.2 hBA
      ⟨p, ⟨hpB, mem_connectedComponentIn hpA⟩⟩⟩⟩


theorem mem_cmpnts_eq_iff_inter_nonempty {A B C : Set X}
    (hB : B ∈ components A) (hC : C ∈ components A) : B = C ↔ (B ∩ C).Nonempty :=
  have f {α β} (hα : α ∈ components A) hβ hαβ : α ⊆ β :=
    mem_cmpnts_maximal hβ (isPreconnected_mem_cmpnts hα) (mem_cmpnts_subset hα) hαβ
  Iff.intro
    (fun hBC ↦ Eq.symm (Set.inter_eq_left.mpr (hBC ▸ subset_rfl : B ⊆ C)) ▸ mem_cmpnts_nonempty hB)
    (fun hBC ↦ Set.eq_of_subset_of_subset (f hB hC hBC) (f hC hB (Set.inter_comm B C ▸ hBC)))


/-
  If the sets A, B have B ⊆ A and C is a connected component of A \ S,
  and K is a connected component of C ∩ B, then K is a connected component of B \ S.
-/
theorem connectedComponentIn_lemma_1 {A B C K S : Set X} (hBA : B ⊆ A) (hC : C ∈ components (A \ S))
    (hK : K ∈ components (C ∩ B)) : K ∈ components (B \ S) := by
  have hCBBS : C ∩ B ⊆ B \ S := fun k hkCB ↦
    ⟨hkCB.2, (Set.inter_subset_inter_left B (mem_cmpnts_subset hC) hkCB).1.2⟩
  have hK2 := hK
  rcases hK with ⟨k, ⟨hkCB, rfl⟩⟩
  exact ⟨k, ⟨hCBBS hkCB,
    Set.eq_of_subset_of_subset
      (mem_cmpnts_maximal hK2 isPreconnected_connectedComponentIn
        (Set.subset_inter_iff.mpr ⟨
          mem_cmpnts_maximal hC isPreconnected_connectedComponentIn
            (subset_trans (connectedComponentIn_subset _ k) (Set.diff_subset_diff_left hBA))
            ⟨k, ⟨mem_connectedComponentIn (hCBBS hkCB), hkCB.1⟩⟩,
          subset_trans (connectedComponentIn_subset _ k) Set.diff_subset⟩)
        ⟨k, ⟨mem_connectedComponentIn (hCBBS hkCB), mem_connectedComponentIn hkCB⟩⟩)
      (connectedComponentIn_mono k hCBBS)⟩⟩


/-
  Let the sets A, B have B ⊆ A.
  Let C1 and C2 be connected components of A \ S and B \ S respectively. Suppose C1 ∩ C2 != {}.
  Then C2 ⊆ C1, and furthermore C2 is a connected component of C1 ∩ B.
-/
theorem connectedComponentIn_lemma_2 {A B C D S : Set X} (hBA : B ⊆ A)
    (hCAS : C ∈ components (A \ S)) (hDBS : D ∈ components (B \ S))
    (hCDinter : (C ∩ D).Nonempty) : D ∈ components (C ∩ B) := by
  rcases hCDinter with ⟨p, hpC, hpD⟩
  have hpB := subset_trans (mem_cmpnts_subset hDBS) Set.diff_subset hpD
  have hKBS := connectedComponentIn_lemma_1 hBA hCAS
    (connectedComponentIn_mem_cmpnts ⟨hpC, hpB⟩)
  have hD : D = connectedComponentIn (B \ S) p := by
    rcases hDBS with ⟨_, _, rfl⟩
    exact connectedComponentIn_eq hpD
  cases hD
  have hpCB : p ∈ connectedComponentIn (C ∩ B) p := mem_connectedComponentIn ⟨hpC, hpB⟩
  exact ⟨p, ⟨⟨hpC, hpB⟩, Set.eq_of_subset_of_subset
    (mem_cmpnts_maximal hDBS isPreconnected_connectedComponentIn
      (mem_cmpnts_subset hKBS) ⟨p, hpCB, hpD⟩)
    (mem_cmpnts_maximal hKBS isPreconnected_connectedComponentIn
      (mem_cmpnts_subset hDBS) ⟨p, hpD, hpCB⟩)⟩⟩


theorem connectedComponentIn_lemma_2_1 {A B C D S : Set X} (hBA : B ⊆ A)
    (hCAS : C ∈ components (A \ S)) (hDBS : D ∈ components (B \ S))
    (hCDinter : (C ∩ D).Nonempty) : D ⊆ C :=
  subset_trans
    (mem_cmpnts_subset (connectedComponentIn_lemma_2 hBA hCAS hDBS hCDinter))
    Set.inter_subset_left


/-
  If A, B are open sets with B ⊆ A and D is a connected component of B \ S,
  then there is a unique connected component K of A \ S with D ⊆ K.
-/
theorem connectedComponentIn_lemma_3 {A B D S : Set X} (hBA : B ⊆ A)
    (hDBS : D ∈ components (B \ S)) : ∃! C ∈ components (A \ S), D ⊆ C := by
  rcases hDBS with ⟨p, hpBS, rfl⟩
  have hpAS : p ∈ A \ S := ⟨hBA hpBS.1, hpBS.2⟩
  use connectedComponentIn (A \ S) p
  have hA1 := connectedComponentIn_mem_cmpnts hpAS
  have hB1 := connectedComponentIn_mem_cmpnts hpBS
  have hA2 := mem_connectedComponentIn hpAS
  have hB2 := mem_connectedComponentIn hpBS
  split_ands
  · exact hA1
  · exact connectedComponentIn_lemma_2_1 hBA hA1 hB1 ⟨p, hA2, hB2⟩
  · rintro H ⟨⟨q, ⟨hqAS, rfl⟩⟩, hDH⟩
    exact connectedComponentIn_eq (hDH hB2)
