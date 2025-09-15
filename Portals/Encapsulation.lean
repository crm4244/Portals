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

theorem nth_Nonempty (hE : Encapsulation E) (n : ℕ) : (E n).Nonempty := by
  rcases hE with ⟨h, _⟩
  exact h n

theorem nth_IsOpen (hE : Encapsulation E) (n : ℕ) : IsOpen (E n) := by
  rcases hE with ⟨_, h, _⟩
  exact h n

theorem nth_closure_nested (hE : Encapsulation E) (n : ℕ) : closure (E (n + 1)) ⊆ E n := by
  rcases hE with ⟨_, _, _, h, _⟩
  exact h n

theorem nested (hE : Encapsulation E) {n m : ℕ} (h : n ≤ m) : E m ⊆ E n := by
  induction m with
  | zero =>
    rw [Nat.le_zero_eq] at h
    rw [h]
  | succ m ih =>
    rw [Nat.le_iff_lt_or_eq] at h
    cases h with
    | inl h =>
      rw [← Nat.le_iff_lt_add_one] at h
      apply subset_trans subset_closure
      apply subset_trans (nth_closure_nested hE m)
      exact ih h
    | inr h =>
      rw [h]

theorem nth_compact_closure (hE : Encapsulation E) (n : Nat) :
    IsCompact (closure (E n)) := by
  have h := nested hE (Nat.zero_le (n-1))
  rcases hE with ⟨_, _, hc0, hn, _⟩
  cases n with
  | zero =>
    exact hc0
  | succ n =>
    apply IsCompact.of_isClosed_subset hc0 isClosed_closure
    apply subset_trans (hn n)
    apply subset_trans h
    exact subset_closure

theorem center_unique (hE : Encapsulation E) {p : X} (hp : IsCenter E p)
    {q : X} (hq : IsCenter E q) : p=q := by
  rcases hE with ⟨_, _, _, _, h⟩
  exact h p hp q hq

theorem center_exists (hE : Encapsulation E) :
    ∃ p, IsCenter E p := by
  have h : (⋂ n, closure (E n)).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n
      exact subset_trans (nth_closure_nested hE n) subset_closure
    · intro n
      obtain ⟨p, hp⟩ := nth_Nonempty hE n
      use p
      apply subset_closure
      exact hp
    · exact nth_compact_closure hE 0
    · intro n
      exact isClosed_closure
  obtain ⟨p, hp⟩ := h
  use p
  unfold IsCenter
  rw [Set.mem_iInter] at hp ⊢
  intro n
  apply Set.mem_of_mem_of_subset (hp (n+1))
  exact nth_closure_nested hE n

noncomputable def center (hE : Encapsulation E) : X :=
  Classical.choose (center_exists hE)

theorem IsCenter_center (hE : Encapsulation E) :
    IsCenter E (center hE) := by
  apply Classical.choose_spec

theorem center_exists_unique (hE : Encapsulation E) :
    ∃! p, IsCenter E p := by
  use center hE
  split_ands
  · apply IsCenter_center
  · intro y hy
    exact center_unique hE hy (IsCenter_center hE)

theorem i_SubSequence_is_Encapsulation (hE : Encapsulation E) {α : ℕ → ℕ} (hα : StrictMono α) :
    Encapsulation (E ∘ α) := by
  split_ands
  · intro n
    exact nth_Nonempty hE (α n)
  · intro n
    exact nth_IsOpen hE (α n)
  · exact nth_compact_closure hE (α 0)
  · have h := hE
    intro n
    specialize hα (Nat.lt_add_one n)
    have hn1 := nth_closure_nested hE (α (n+1) - 1)
    have hα2 := Nat.lt_of_le_of_lt (Nat.zero_le (α n)) hα
    rw [Nat.sub_add_cancel] at hn1
    · apply subset_trans hn1
      apply nested h
      rw [Nat.le_sub_one_iff_lt hα2]
      exact hα
    apply Nat.le_of_pred_lt hα2
  · intro p hp q hq
    apply center_unique hE
    all_goals unfold IsCenter at hp hq ⊢
    all_goals rw [Set.mem_iInter] at hp hq ⊢
    all_goals intro n
    · exact nested hE (StrictMono.id_le hα n) (hp n)
    · exact nested hE (StrictMono.id_le hα n) (hq n)


end Encapsulation
