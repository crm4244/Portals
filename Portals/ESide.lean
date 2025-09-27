import Portals.Encapsulation
import Portals.Basic
import Mathlib.Topology.Connected.LocallyConnected



variable {X : Type} [hX : TopologicalSpace X]


class ESide.IsGenerator (S : Set X) (a : ℕ → Set X) (E : ℕ → Set X) where
  isEncapsulation : Encapsulation E
  nth_mem_cmpnts : ∀ n, a n ∈ components ((E n) \ S)


class ESide (S : Set X) (a : ℕ → Set X) where
  exists_generator : ∃ E, ESide.IsGenerator S a E
  nth_nested (n : ℕ) : a (n + 1) ⊆ a n


def ESide.isCenter (a : ℕ → Set X) (p : X) := p ∈ ⋂ n, closure (a n)
def ESide.weakly_touches (a : ℕ → Set X) (A : Set X) := ∀ n, (a n ∩ A).Nonempty
def ESide.strongly_touches (a : ℕ → Set X) (A : Set X) := ∃ n, a n ⊆ A
def ESide.touches (a b : ℕ → Set X) := ∀ n, (a n ∩ b n).Nonempty


variable {S : Set X} {a : ℕ → Set X}



namespace ESide



theorem nth_subset_generator {E : ℕ → Set X} (hE : IsGenerator S a E) (n : ℕ) : a n ⊆ E n :=
  fun _ hp => (mem_cmpnts_subset (hE.nth_mem_cmpnts n) hp).1


theorem nth_nonempty (ha : ESide S a) (n : ℕ) : (a n).Nonempty :=
  match ha.exists_generator with | ⟨_, hE⟩ => mem_cmpnts_nonempty (hE.nth_mem_cmpnts n)


theorem nth_isPreconnected (ha : ESide S a) (n : ℕ) : IsPreconnected (a n) :=
  match ha.exists_generator with | ⟨_, hE⟩ => isPreconnected_mem_cmpnts (hE.nth_mem_cmpnts n)


theorem nth_isConnected (ha : ESide S a) (n : ℕ) : IsConnected (a n) :=
  match ha.exists_generator with | ⟨_, hE⟩ => isConnected_mem_cmpnts (hE.nth_mem_cmpnts n)


theorem nth_isOpen [hX_locallyConnected : LocallyConnectedSpace X] [hS : IsClosed S]
    (ha : ESide S a) (n : ℕ) : IsOpen (a n) :=
  match ha.exists_generator with
  | ⟨_, hE⟩ => match hE.nth_mem_cmpnts n with
    | ⟨_, hp⟩ => hp.2 ▸ IsOpen.connectedComponentIn
      (IsOpen.sdiff (hE.isEncapsulation.nth_IsOpen n) hS)


theorem not_mem_surface_of_mem_nth (ha : ESide S a) {n : ℕ} {p : X} (hp : p ∈ a n) : p ∉ S :=
  match ha.exists_generator with
  | ⟨_, hE⟩ => (mem_cmpnts_subset (hE.nth_mem_cmpnts n) hp).2


theorem center_exists (ha : ESide S a) : ∃ p, isCenter a p :=
  match ha.exists_generator with
  | ⟨_, hE⟩ => IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => closure (a n))
    (fun n => closure_mono (ha.nth_nested n))
    (fun n => closure_nonempty_iff.mpr (mem_cmpnts_nonempty (hE.nth_mem_cmpnts n)))
    (IsCompact.of_isClosed_subset hE.isEncapsulation.zeroth_compact_closure
      isClosed_closure (closure_mono (nth_subset_generator hE 0)))
    (fun _ => isClosed_closure)


theorem isCenter_iff_isCenter_generator (ha : ESide S a) {E : ℕ → Set X}
    (hE : IsGenerator S a E) (p : X) : isCenter a p ↔ Encapsulation.isCenter E p :=
  have h : ∀ x, isCenter a x → Encapsulation.isCenter E x :=
    fun _ hx => Set.mem_iInter.mpr fun n => subset_trans
    (closure_mono (nth_subset_generator hE (n+1)))
    (hE.isEncapsulation.nth_closure_nested n) (Set.mem_iInter.mp hx (n+1))
  Iff.intro (h p) fun hp => match center_exists ha with
    | ⟨c, hc⟩ => hE.isEncapsulation.center_unique hp (h c hc) ▸ hc


theorem center_unique (ha : ESide S a) {p : X} (hp : isCenter a p)
    {q : X} (hq : isCenter a q) : p=q :=
  match ha.exists_generator with
  | ⟨_, hE⟩ =>
    have f := fun r hr => (isCenter_iff_isCenter_generator ha hE r).mp hr
    hE.isEncapsulation.center_unique (f p hp) (f q hq)


theorem center_exists_unique (ha : ESide S a) : ∃! p, isCenter a p :=
  match center_exists ha with | ⟨p, hp⟩ => ⟨p, ⟨hp, fun _ hq => center_unique ha hq hp⟩⟩


noncomputable def center (ha : ESide S a) := Classical.choose (center_exists ha)


theorem isCenter_center (ha : ESide S a) : isCenter a (center ha) :=
  Classical.choose_spec (center_exists ha)


theorem center_eq_generator_center (ha : ESide S a) {E : ℕ → Set X} (hE : IsGenerator S a E) :
    center ha = hE.isEncapsulation.center :=
  center_unique ha (isCenter_center ha) (
    (isCenter_iff_isCenter_generator ha hE hE.isEncapsulation.center).mpr
    hE.isEncapsulation.isCenter_center)


theorem nested (ha : ESide S a) {n m : ℕ} (h : n ≤ m) : a m ⊆ a n := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ m ih => cases Nat.le_add_one_iff.mp h with
    | inr hr => rw [hr]
    | inl hl => exact subset_trans (ha.nth_nested m) (ih hl)


theorem instESide_subsequence (ha : ESide S a) {α : ℕ → ℕ} (hα : StrictMono α) : ESide S (a ∘ α) :=
  match ha.exists_generator with
  | ⟨E, hE⟩ => ESide.mk
    ⟨E ∘ α, IsGenerator.mk
      (Encapsulation.instEncapsulation_subsequence hE.isEncapsulation hα)
      (fun n => hE.nth_mem_cmpnts (α n))⟩
    (fun n => nested ha ((StrictMono.le_iff_le hα).mpr (Nat.le_add_right n 1)))


theorem strongly_touches_of_center_mem_IsOpen (ha : ESide S a) {A : Set X} (hA : IsOpen A)
    (hcA : center ha ∈ A) : strongly_touches a A := match ha.exists_generator with
  | ⟨_, hE⟩ =>
    have hnA := hE.isEncapsulation.exists_subset_of_center_mem_IsOpen hA
      (center_eq_generator_center ha hE ▸ hcA)
    match hnA with | ⟨n, hn⟩ => ⟨n, subset_trans (nth_subset_generator hE n) hn⟩


omit hX in theorem nth_strongly_touches_self (n : ℕ) : strongly_touches a (a n) :=
  ⟨n, subset_refl (a n)⟩


theorem weakly_touches_of_strongly_touches (ha : ESide S a) {A : Set X}
    (hA : strongly_touches a A) : weakly_touches a A :=
  fun n => match hA with
  | ⟨m, hm⟩ => match (nth_nonempty ha (Nat.max n m)) with
  | ⟨p, hp⟩ => ⟨p, ⟨nested ha (Nat.le_max_left n m) hp, hm (nested ha (Nat.le_max_right n m) hp)⟩⟩


omit hX in theorem strongly_touches_of_strongly_touches_subset {A B : Set X}
    (hA : strongly_touches a A) (hAB : A ⊆ B) : strongly_touches a B :=
  match hA with | ⟨n, hn⟩ => ⟨n, subset_trans hn hAB⟩


omit hX in theorem weakly_touches_of_weakly_touches_subset {A B : Set X}
    (hA : weakly_touches a A) (hAB : A ⊆ B) : weakly_touches a B :=
  fun n => match hA n with | ⟨p, hp⟩ => ⟨p, ⟨hp.1, hAB hp.2⟩⟩


theorem inter_Nonempty_of_strongly_touches (ha : ESide S a) {A B : Set X}
    (hA : strongly_touches a A) (hB : strongly_touches a B) : (A ∩ B).Nonempty :=
  match hA with
  | ⟨n, hn⟩ => match hB with
  | ⟨m, hm⟩ =>
    have h : a (Nat.max n m) ⊆ A ∩ B := (fun _ hp =>
      ⟨hn (nested ha (Nat.le_max_left n m) hp), hm (nested ha (Nat.le_max_right n m) hp)⟩)
    Set.Nonempty.mono h (nth_nonempty ha (Nat.max n m))


theorem center_mem_closure_of_weakly_touches (ha : ESide S a) {A : Set X}
    (hA : weakly_touches a A) : center ha ∈ closure A :=
  mem_closure_iff.mpr fun _ hB hcB => match strongly_touches_of_center_mem_IsOpen ha hB hcB with
    | ⟨n, hn⟩ => match hA n with
      | ⟨p, hp⟩ => ⟨p, ⟨hn hp.1, hp.2⟩⟩


theorem exists_mem_cmpnts_diff_surface_strongly_touches_of_center_mem_IsOpen (ha : ESide S a)
  {A : Set X} (hA : IsOpen A) (hcA : center ha ∈ A) :
    ∃ B ∈ components (A \ S), strongly_touches a B :=
  match strongly_touches_of_center_mem_IsOpen ha hA hcA with
  | ⟨n, hn⟩ =>
    have h : a n ⊆ A \ S := fun _ hp => ⟨hn hp, not_mem_surface_of_mem_nth ha hp⟩
    match exists_subset_mem_cmpnts_of_subset h (nth_isConnected ha n) with
    | ⟨B, hB⟩ => ⟨B, ⟨hB.1, ⟨n, hB.2⟩⟩⟩


theorem unique_mem_cmpnts_diff_surface_weakly_touches_of_center_mem_IsOpen (ha : ESide S a)
    {A B C : Set X} (hA : IsOpen A) (hcA : center ha ∈ A)
    (hBAS : B ∈ components (A \ S)) (hBa : weakly_touches a B)
    (hCAS : C ∈ components (A \ S)) (hCa : weakly_touches a C) : B = C :=
  match exists_mem_cmpnts_diff_surface_strongly_touches_of_center_mem_IsOpen ha hA hcA with
  | ⟨D, hD⟩ => match hD.2 with
    | ⟨n, hnD⟩ =>
      have f α (hαAS : α ∈ components (A \ S)) (hαa : weakly_touches a α) : α = D :=
        (mem_cmpnts_eq_iff_inter_nonempty hαAS hD.1).mpr
        (Set.inter_comm D α ▸ Set.Nonempty.mono (Set.inter_subset_inter_left α hnD) (hαa n))
      Eq.trans (f B hBAS hBa) (Eq.symm (f C hCAS hCa))


theorem unique_mem_cmpnts_diff_surface_strongly_touches_of_center_mem_IsOpen (ha : ESide S a)
    {A B C : Set X} (hA : IsOpen A) (hcA : center ha ∈ A)
    (hBAS : B ∈ components (A \ S)) (hBa : strongly_touches a B)
    (hCAS : C ∈ components (A \ S)) (hCa : strongly_touches a C) : B = C :=
  unique_mem_cmpnts_diff_surface_weakly_touches_of_center_mem_IsOpen ha hA hcA
    hBAS (weakly_touches_of_strongly_touches ha hBa)
    hCAS (weakly_touches_of_strongly_touches ha hCa)


theorem touches_iff_forall_weakly_touches (ha : ESide S a) {b : ℕ → Set X} (hb : ESide S b) :
    touches a b ↔ ∀ n, weakly_touches a (b n) :=
  Iff.intro
    (fun h n m => match h (Nat.max n m) with
      | ⟨p, hp⟩ => ⟨p, ⟨
        nested ha (Nat.le_max_right n m) hp.1,
        nested hb (Nat.le_max_left n m) hp.2⟩⟩)
    (fun h n => h n n)


theorem center_eq_center_of_touches [hXT2 : T2Space X] (ha : ESide S a) {b : ℕ → Set X}
    (hb : ESide S b) (hab : touches a b) : center ha = center hb :=
  Classical.byContradiction (fun hCenterNeq => match hXT2.t2 hCenterNeq with
  | ⟨_, _, hU, hV, haU, hbV, hUV⟩ => match strongly_touches_of_center_mem_IsOpen ha hU haU with
  | ⟨k, hk⟩ => match strongly_touches_of_center_mem_IsOpen hb hV hbV with
  | ⟨j, hj⟩ => match (touches_iff_forall_weakly_touches ha hb).mp hab j k with
  | ⟨_, hp⟩ => Set.disjoint_iff_forall_ne.mp hUV (hk hp.1) (hj hp.2) rfl)


theorem forall_weakly_touches_iff_forall_strongly_touches [hXT2 : T2Space X]
  (ha : ESide S a) {b : ℕ → Set X} (hb : ESide S b) :
    (∀ n, weakly_touches a (b n)) ↔ (∀ n, strongly_touches a (b n)) :=
  Iff.intro
    (fun hWeak n => Classical.byContradiction (fun hStrong =>
      match ha.exists_generator with
      | ⟨Ea, hEa⟩ => match hb.exists_generator with
      | ⟨Eb, hEb⟩ =>
      have hGenCenterEq : hEa.isEncapsulation.center = hEb.isEncapsulation.center := by
        rw [← center_eq_generator_center ha hEa, ← center_eq_generator_center hb hEb]
        exact center_eq_center_of_touches ha hb
          ((touches_iff_forall_weakly_touches ha hb).mpr hWeak)
      match (hEa.isEncapsulation.exists_subset_of_center_mem_IsOpen
        (hEb.isEncapsulation.nth_IsOpen n)
        (hGenCenterEq ▸ hEb.isEncapsulation.center_mem_nth n)) with
      | ⟨k, hk⟩ => match Set.not_subset.mp (not_exists.mp hStrong k) with
      | ⟨p, hp⟩ => hp.2 (mem_cmpnts_maximal (hEb.nth_mem_cmpnts n) (ha.nth_isPreconnected k)
        (fun p hp => ⟨hk (nth_subset_generator hEa k hp), not_mem_surface_of_mem_nth ha hp⟩)
        (hWeak n k) hp.1)))
    (fun h n => weakly_touches_of_strongly_touches ha (h n))


theorem touches_iff_forall_strongly_touches [hXT2 : T2Space X] (ha : ESide S a)
    {b : ℕ → Set X} (hb : ESide S b) : touches a b ↔ ∀ n, strongly_touches a (b n) :=
  Iff.trans
    (touches_iff_forall_weakly_touches ha hb)
    (forall_weakly_touches_iff_forall_strongly_touches ha hb)



end ESide



theorem Encapsulation.isCenter_ESide_center (ha : ESide S a) {E} (hE : ESide.IsGenerator S a E) :
    Encapsulation.isCenter E (ESide.center ha) :=
  (ha.isCenter_iff_isCenter_generator hE ha.center).mp (ESide.isCenter_center ha)
