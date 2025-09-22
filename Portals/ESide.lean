import Portals.Encapsulation
import Portals.Basic



variable {X : Type} [hX : TopologicalSpace X]


class ESide.IsGenerator (S : Set X) (a : ℕ → Set X) (E : ℕ → Set X) where
  isEncapsulation : Encapsulation E
  nth_mem_cmpnts : ∀ n, a n ∈ components ((E n) \ S)


class ESide (S : Set X) (a : ℕ → Set X) where
  exists_generator : ∃ E, ESide.IsGenerator S a E
  nth_nested (n : ℕ) : a (n + 1) ⊆ a n


def ESide.isCenter (a : ℕ → Set X) (p : X) := p ∈ ⋂ n, closure (a n)


variable {S : Set X} {a : ℕ → Set X}



namespace ESide



theorem nth_subset_generator {E} (hE : IsGenerator S a E) (n : ℕ) : a n ⊆ E n :=
  fun _ hp => (mem_cmpnts_subset (hE.nth_mem_cmpnts n) hp).1


theorem center_exists (ha : ESide S a) : ∃ p, isCenter a p :=
  match ha.exists_generator with
  | ⟨_, hE⟩ => IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (a n))
    (fun n => closure_mono (ha.nth_nested n))
    (fun n => closure_nonempty_iff.mpr (mem_cmpnts_Nonempty (hE.nth_mem_cmpnts n)))
    (IsCompact.of_isClosed_subset hE.isEncapsulation.zeroth_compact_closure
      isClosed_closure (closure_mono (nth_subset_generator hE 0)))
    (fun _ => isClosed_closure)


theorem isCenter_iff_isCenter_generator (ha : ESide S a) {E} (hE : IsGenerator S a E) (p : X) :
    isCenter a p ↔ Encapsulation.isCenter E p :=
  have h : ∀ x, isCenter a x → Encapsulation.isCenter E x :=
    fun _ hx => Set.mem_iInter.mpr fun n => subset_trans
    (closure_mono (nth_subset_generator hE (n+1)))
    (hE.isEncapsulation.nth_closure_nested n) (Set.mem_iInter.mp hx (n+1))
  Iff.intro (h p) fun hp => match center_exists ha with
    | ⟨c, hc⟩ => hE.isEncapsulation.center_unique hp (h c hc) ▸ hc


theorem center_unique (ha : ESide S a) : ∀ p, isCenter a p → ∀ q, isCenter a q → p=q :=
  match ha.exists_generator with
  | ⟨_, hE⟩ =>
    have f := fun r hr => (isCenter_iff_isCenter_generator ha hE r).mp hr
    fun p hp q hq => hE.isEncapsulation.center_unique (f p hp) (f q hq)


theorem center_exists_unique (ha : ESide S a) : ∃! p, isCenter a p :=
  match center_exists ha with | ⟨p, hp⟩ => ⟨p, ⟨hp, fun q hq => center_unique ha q hq p hp⟩⟩


noncomputable def center (ha : ESide S a) := Classical.choose (center_exists ha)


theorem isCenter_center (ha : ESide S a) : isCenter a (center ha) :=
  Classical.choose_spec (center_exists ha)


theorem nested (ha : ESide S a) {n m : ℕ} (h : n ≤ m) : a m ⊆ a n := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih => cases Nat.le_add_one_iff.mp h with
    | inr hr => rw [hr]
    | inl hl => exact subset_trans (ha.nth_nested m) (ih hl)



end ESide



theorem Encapsulation.isCenter_ESide_center (ha : ESide S a) {E} (hE : ESide.IsGenerator S a E) :
    Encapsulation.isCenter E (ESide.center ha) :=
  (ha.isCenter_iff_isCenter_generator hE ha.center).mp (ESide.isCenter_center ha)
