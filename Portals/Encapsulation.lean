import MathLib.Topology.Sets.Closeds

variable {X : Type} [hX : TopologicalSpace X]

def Encapsulation.IsCenter (E : ℕ → Set X) (p : X) := p ∈ ⋂ n, E n

def Encapsulation (E : ℕ → Set X) :=
  (∀ n, (E n).Nonempty) ∧
  (∀ n, IsOpen (E n)) ∧
  (IsCompact (closure (E 0))) ∧
  (∀ n, closure (E (n + 1)) ⊆ E n) ∧
  (∀ (p q : X), Encapsulation.IsCenter E p → Encapsulation.IsCenter E q → p=q)


namespace Encapsulation


theorem center_exists {E : ℕ → Set X} :
    Encapsulation E → ∃ p, IsCenter E p := by
  intro hE
  rcases hE with ⟨hne, ho, hc0, hn, _⟩
  have h : (⋂ n, closure (E n)).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · intro n
      exact subset_trans (hn n) subset_closure
    · intro n
      obtain ⟨p, hp⟩ := hne n
      use p
      apply subset_closure
      exact hp
    · exact hc0
    · intro n
      exact isClosed_closure
  obtain ⟨p, hp⟩ := h
  use p
  unfold IsCenter
  rw [Set.mem_iInter] at hp ⊢
  intro n
  apply Set.mem_of_mem_of_subset (hp (n+1))
  exact hn n

theorem center_unique {E : ℕ → Set X} :
    Encapsulation E → ∀ (p q : X), IsCenter E p → IsCenter E q → p=q := by
  intro hE
  rcases hE with ⟨_, _, _, _, h⟩
  exact h

noncomputable def center {E : ℕ → Set X} (hE : Encapsulation E) : X :=
  Classical.choose (center_exists hE)

theorem IsCenter_center {E : ℕ → Set X} (hE : Encapsulation E) :
    IsCenter E (center hE) := by
  apply Classical.choose_spec

theorem center_exists_unique (E : ℕ → Set X) :
    Encapsulation E → ∃! p, IsCenter E p := by
  intro hE
  use center hE
  split_ands
  · apply IsCenter_center
  · intro y hy
    exact center_unique hE y (center hE) hy (IsCenter_center hE)

theorem nested {E : ℕ → Set X} : Encapsulation E → ∀ n m,  n ≤ m → E m ⊆ E n := by
  intro hE n m h
  rcases hE with ⟨_, _, _, hn, _⟩
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
      apply subset_trans (hn m)
      exact ih h
    | inr h =>
      rw [h]

theorem compact_closures {E : ℕ → Set X} :
    ∀ n, Encapsulation E → IsCompact (closure (E n)) := by
  intro n hE
  cases n with
  | zero =>
    rcases hE with ⟨_, _, hc0, _⟩
    exact hc0
  | succ n =>
    have h := nested hE 0 n (Nat.zero_le n)
    rcases hE with ⟨_, _, hc0, hn, _⟩
    apply IsCompact.of_isClosed_subset hc0 isClosed_closure
    apply subset_trans (hn n)
    apply subset_trans h
    exact subset_closure

theorem i_SubSequence_is_encapsulation {E : ℕ → Set X} {α : ℕ → ℕ} :
    Encapsulation E → StrictMono α → Encapsulation (E ∘ α) := by
  intro hE hα
  split_ands
  · rcases hE with ⟨hne, ho, hc0, hn, hcu⟩
    intro n
    exact hne (α n)
  · rcases hE with ⟨hne, ho, hc0, hn, hcu⟩
    intro n
    exact ho (α n)
  · exact compact_closures (α 0) hE
  · have h := hE
    rcases hE with ⟨_, _, _, hn, _⟩
    intro n
    specialize hα (Nat.lt_add_one n)
    have hn1 := hn (α (n+1) - 1)
    have hα2 := Nat.lt_of_le_of_lt (Nat.zero_le (α n)) hα
    rw [Nat.sub_add_cancel] at hn1
    · apply subset_trans hn1
      apply nested h
      rw [Nat.le_sub_one_iff_lt hα2]
      exact hα
    apply Nat.le_of_pred_lt hα2
  · have hE2 := hE
    rcases hE with ⟨hne, ho, hc0, hn, hcu⟩
    intro p q hp hq
    apply hcu
    all_goals unfold IsCenter at hp hq ⊢
    all_goals rw [Set.mem_iInter] at hp hq ⊢
    all_goals intro n
    · exact nested hE2 n (α n) (StrictMono.id_le hα n) (hp n)
    · exact nested hE2 n (α n) (StrictMono.id_le hα n) (hq n)


end Encapsulation
