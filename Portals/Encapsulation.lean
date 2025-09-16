import MathLib.Topology.Sets.Closeds




variable {X : Type} [hX : TopologicalSpace X]

def Encapsulation.IsCenter (E : ℕ → Set X) (p : X) := p ∈ ⋂ n, E n

def Encapsulation (E : ℕ → Set X) :=
  (∀ n, (E n).Nonempty) ∧
  (∀ n, IsOpen (E n)) ∧
  (IsCompact (closure (E 0))) ∧
  (∀ n, closure (E (n + 1)) ⊆ E n) ∧
  (∀ p, Encapsulation.IsCenter E p → (∀ q, Encapsulation.IsCenter E q → p=q))

variable {E : ℕ → Set X}




namespace Encapsulation


theorem nth_Nonempty (hE : Encapsulation E) (n : ℕ) : (E n).Nonempty := hE.1 n

theorem nth_IsOpen (hE : Encapsulation E) (n : ℕ) : IsOpen (E n) := hE.2.1 n

theorem nth_closure_nested (hE : Encapsulation E) (n : ℕ) : closure (E (n + 1)) ⊆ E n :=
  hE.2.2.2.1 n

theorem nested (hE : Encapsulation E) {n m : ℕ} (h : n ≤ m) : E m ⊆ E n := by
  induction m with
  | zero =>
    rw [Nat.le_zero_eq] at h
    rw [h]
  | succ m ih =>
    rw [Nat.le_iff_lt_or_eq] at h
    cases h with
    | inl h =>
      exact subset_trans subset_closure (
        subset_trans (nth_closure_nested hE m) (ih (Nat.le_iff_lt_add_one.mpr h)))
    | inr h =>
      rw [h]

theorem nth_compact_closure (hE : Encapsulation E) (n : Nat) :
    IsCompact (closure (E n)) :=
  match n with
  | 0 =>
    hE.2.2.1
  | n+1 =>
    IsCompact.of_isClosed_subset hE.2.2.1 isClosed_closure (
      subset_trans (nth_closure_nested hE n) (
        subset_trans (nested hE (Nat.zero_le n)) subset_closure))

theorem center_unique (hE : Encapsulation E) {p : X} (hp : IsCenter E p)
    {q : X} (hq : IsCenter E q) : p=q := hE.2.2.2.2 p hp q hq

theorem center_exists (hE : Encapsulation E) :
    ∃ p, IsCenter E p := by
  have h : (⋂ n, closure (E n)).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · exact fun n => subset_trans (nth_closure_nested hE n) subset_closure
    · exact fun n => match nth_Nonempty hE n with | ⟨p, hp⟩ => ⟨p, subset_closure hp⟩
    · exact nth_compact_closure hE 0
    · exact fun n => isClosed_closure
  exact match h with | ⟨p, hp⟩ => ⟨p, Set.mem_iInter.mpr (
    fun n => Set.mem_of_mem_of_subset (Set.mem_iInter.mp hp (n+1)) (nth_closure_nested hE n))⟩

noncomputable def center (hE : Encapsulation E) : X := Classical.choose (center_exists hE)

theorem IsCenter_center (hE : Encapsulation E) : IsCenter E (center hE) :=
  Classical.choose_spec (center_exists hE)

theorem center_exists_unique (hE : Encapsulation E) :
    ∃! p, IsCenter E p :=
    ⟨center hE, IsCenter_center hE, fun _ h => center_unique hE h (IsCenter_center hE)⟩

theorem i_SubSequence_is_Encapsulation (hE : Encapsulation E) {α : ℕ → ℕ} (hα : StrictMono α) :
    Encapsulation (E ∘ α) := by
  split_ands
  · exact fun n => nth_Nonempty hE (α n)
  · exact fun n => nth_IsOpen hE (α n)
  · exact nth_compact_closure hE (α 0)
  · intro n
    specialize hα (Nat.lt_add_one n)
    have hn1 := nth_closure_nested hE (α (n+1) - 1)
    have hα2 := Nat.lt_of_le_of_lt (Nat.zero_le (α n)) hα
    rw [Nat.sub_add_cancel] at hn1
    · exact subset_trans hn1 (nested hE ((Nat.le_sub_one_iff_lt hα2).mpr hα))
    · exact Nat.le_of_pred_lt hα2
  · intro p hp q hq
    apply center_unique hE
    · exact Set.mem_iInter.mpr (fun n => nested hE (StrictMono.id_le hα n) (Set.mem_iInter.mp hp n))
    · exact Set.mem_iInter.mpr (fun n => nested hE (StrictMono.id_le hα n) (Set.mem_iInter.mp hq n))


end Encapsulation
