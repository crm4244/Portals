import Mathlib.Topology.Sets.Closeds



variable {X : Type} [hX : TopologicalSpace X]


def Encapsulation.isCenter (E : ℕ → Set X) (p : X) := p ∈ ⋂ n, E n


class Encapsulation (E : ℕ → Set X) where
  nth_Nonempty (n : ℕ) : (E n).Nonempty
  nth_IsOpen (n : ℕ) : IsOpen (E n)
  zeroth_compact_closure : IsCompact (closure (E 0))
  nth_closure_nested (n : ℕ) : closure (E (n + 1)) ⊆ E n
  center_unique {p : X} (hp : Encapsulation.isCenter E p)
    {q : X} (hq : Encapsulation.isCenter E q) : p = q


variable {E : ℕ → Set X}



namespace Encapsulation



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
        subset_trans (nth_closure_nested m) (ih (Nat.le_iff_lt_add_one.mpr h)))
    | inr h =>
      rw [h]


theorem nth_compact_closure (hE : Encapsulation E) (n : Nat) :
    IsCompact (closure (E n)) :=
  match n with
  | 0 => zeroth_compact_closure
  | n + 1 =>
    IsCompact.of_isClosed_subset zeroth_compact_closure isClosed_closure (
      subset_trans (nth_closure_nested n) (
        subset_trans (nested hE (Nat.zero_le n)) subset_closure))


theorem center_exists (hE : Encapsulation E) :
    ∃ p, isCenter E p := by
  have h : (⋂ n, closure (E n)).Nonempty := by
    apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    · exact fun n => subset_trans (nth_closure_nested n) subset_closure
    · exact fun n => match nth_Nonempty n with | ⟨p, hp⟩ => ⟨p, subset_closure hp⟩
    · exact nth_compact_closure hE 0
    · exact fun n => isClosed_closure
  exact match h with | ⟨p, hp⟩ => ⟨p, Set.mem_iInter.mpr (
    fun n => Set.mem_of_mem_of_subset (Set.mem_iInter.mp hp (n+1)) (nth_closure_nested n))⟩


theorem instEncapsulation_subsequence (hE : Encapsulation E) {α : ℕ → ℕ} (hα : StrictMono α) :
    Encapsulation (E ∘ α) := Encapsulation.mk
  (fun n => hE.nth_Nonempty (α n))
  (fun n => hE.nth_IsOpen (α n))
  (nth_compact_closure hE (α 0))
  ( by
    intro n
    specialize hα (Nat.lt_add_one n)
    have hn1 := hE.nth_closure_nested (α (n+1) - 1)
    have hα2 := Nat.lt_of_le_of_lt (Nat.zero_le (α n)) hα
    rw [Nat.sub_add_cancel] at hn1
    · exact subset_trans hn1 (nested hE ((Nat.le_sub_one_iff_lt hα2).mpr hα))
    · exact Nat.le_of_pred_lt hα2)
  (@fun p hp q hq =>
    let hx := fun x (hx : isCenter (E ∘ α) x) => Set.mem_iInter.mpr (
      fun n => nested hE (StrictMono.id_le hα n) (Set.mem_iInter.mp hx n))
    hE.center_unique (hx p hp) (hx q hq))


noncomputable def center (hE : Encapsulation E) : X := Classical.choose (@center_exists _ _ _ hE)


theorem isCenter_center (hE : Encapsulation E) : isCenter E (center hE) :=
  Classical.choose_spec (center_exists hE)


theorem center_exists_unique (hE : Encapsulation E) : ∃! p, isCenter E p :=
    ⟨center hE, isCenter_center hE, fun _ h => center_unique h (isCenter_center hE)⟩



/-
  Let O[n] be an encapsulation of a point P in S,and let A be an open neighborhood of P.
  Then there is a k>0 with O[k] ⊆ A.

  Proof. Fix n>0. We have cl(O[n] \ A) ⊆ cl(O[n]) compact, and cl(O[n+1] \ A) ⊆ cl(O[n] \ A).
  Note that Intersection(cl(O[n] \ A)) ⊇ cl(Intersection(O[n] \ A)) =
  cl(Intersection(O[n]) \ A) = cl({P} \ A) = {}.
  We may apply Cantor’s Intersection Theorem in the contrapositive form
  to see that there are only finitely many n with strict inclusion cl(O[n+1] \ A) ⊂ cl(O[n] \ A).
  Let k>0 have cl(O[m+1] \ A) = cl(O[m] \ A) for all m >= k. Now, consider the set B = cl(O[k] \ A).
  If n < k, we have B = cl(O[k] \ A) ⊆ cl(O[n] \ A) by nesting.
  If n >= k we have B ⊆ B = cl(O[k] \ A) = cl(O[n] \ A).
  So, B ⊆ cl(O[n] \ A) ∀ n>0 and B ⊆ Intersection(cl(O[n] \ A)) ⊆ Intersection(cl(O[n])) = {P}.
  To see that P not in B = cl(O[k] \ A), note that P is in the interiors of O[k] and A.
  Finally, we have B empty and so O[k] \ A ⊆ cl(O[k] \ A) = B = {}, which means O[k] ⊆ A as desired.

  QED
-/
--theorem TODO


end Encapsulation
