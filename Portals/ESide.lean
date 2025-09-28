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
def ESide.wtouches (a : ℕ → Set X) (A : Set X) := ∀ n, (a n ∩ A).Nonempty
def ESide.stouches (a : ℕ → Set X) (A : Set X) := ∃ n, a n ⊆ A
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
    {q : X} (hq : isCenter a q) : p = q :=
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


theorem stouches_of_center_mem_IsOpen (ha : ESide S a) {A : Set X} (hA : IsOpen A)
    (hcA : center ha ∈ A) : stouches a A := match ha.exists_generator with
  | ⟨_, hE⟩ =>
    have hnA := hE.isEncapsulation.exists_subset_of_center_mem_IsOpen hA
      (center_eq_generator_center ha hE ▸ hcA)
    match hnA with | ⟨n, hn⟩ => ⟨n, subset_trans (nth_subset_generator hE n) hn⟩


omit hX in theorem nth_stouches_self (n : ℕ) : stouches a (a n) :=
  ⟨n, subset_refl (a n)⟩


theorem wtouches_of_stouches (ha : ESide S a) {A : Set X}
    (hA : stouches a A) : wtouches a A :=
  fun n => match hA with
  | ⟨m, hm⟩ => match (nth_nonempty ha (Nat.max n m)) with
  | ⟨p, hp⟩ => ⟨p, ⟨nested ha (Nat.le_max_left n m) hp, hm (nested ha (Nat.le_max_right n m) hp)⟩⟩


omit hX in theorem stouches_of_stouches_subset {A B : Set X}
    (hA : stouches a A) (hAB : A ⊆ B) : stouches a B :=
  match hA with | ⟨n, hn⟩ => ⟨n, subset_trans hn hAB⟩


omit hX in theorem wtouches_of_wtouches_subset {A B : Set X}
    (hA : wtouches a A) (hAB : A ⊆ B) : wtouches a B :=
  fun n => match hA n with | ⟨p, hp⟩ => ⟨p, ⟨hp.1, hAB hp.2⟩⟩


theorem inter_nonempty_of_stouches (ha : ESide S a) {A B : Set X}
    (hA : stouches a A) (hB : stouches a B) : (A ∩ B).Nonempty :=
  match hA with
  | ⟨n, hn⟩ => match hB with
  | ⟨m, hm⟩ =>
    have h : a (Nat.max n m) ⊆ A ∩ B := (fun _ hp =>
      ⟨hn (nested ha (Nat.le_max_left n m) hp), hm (nested ha (Nat.le_max_right n m) hp)⟩)
    Set.Nonempty.mono h (nth_nonempty ha (Nat.max n m))


theorem center_mem_closure_of_wtouches (ha : ESide S a) {A : Set X}
    (hA : wtouches a A) : center ha ∈ closure A :=
  mem_closure_iff.mpr fun _ hB hcB => match stouches_of_center_mem_IsOpen ha hB hcB with
    | ⟨n, hn⟩ => match hA n with
      | ⟨p, hp⟩ => ⟨p, ⟨hn hp.1, hp.2⟩⟩


theorem exists_mem_cmpnts_diff_surface_stouches_of_center_mem_IsOpen (ha : ESide S a)
  {A : Set X} (hA : IsOpen A) (hcA : center ha ∈ A) :
    ∃ B ∈ components (A \ S), stouches a B :=
  match stouches_of_center_mem_IsOpen ha hA hcA with
  | ⟨n, hn⟩ =>
    have h : a n ⊆ A \ S := fun _ hp => ⟨hn hp, not_mem_surface_of_mem_nth ha hp⟩
    match exists_subset_mem_cmpnts_of_subset h (nth_isConnected ha n) with
    | ⟨B, hB⟩ => ⟨B, ⟨hB.1, ⟨n, hB.2⟩⟩⟩


theorem unique_mem_cmpnts_diff_surface_wtouches_of_center_mem_IsOpen (ha : ESide S a)
    {A B C : Set X} (hA : IsOpen A) (hcA : center ha ∈ A)
    (hBAS : B ∈ components (A \ S)) (hBa : wtouches a B)
    (hCAS : C ∈ components (A \ S)) (hCa : wtouches a C) : B = C :=
  match exists_mem_cmpnts_diff_surface_stouches_of_center_mem_IsOpen ha hA hcA with
  | ⟨D, hD⟩ => match hD.2 with
    | ⟨n, hnD⟩ =>
      have f α (hαAS : α ∈ components (A \ S)) (hαa : wtouches a α) : α = D :=
        (mem_cmpnts_eq_iff_inter_nonempty hαAS hD.1).mpr
        (Set.inter_comm D α ▸ Set.Nonempty.mono (Set.inter_subset_inter_left α hnD) (hαa n))
      Eq.trans (f B hBAS hBa) (Eq.symm (f C hCAS hCa))


theorem unique_mem_cmpnts_diff_surface_stouches_of_center_mem_IsOpen (ha : ESide S a)
    {A B C : Set X} (hA : IsOpen A) (hcA : center ha ∈ A)
    (hBAS : B ∈ components (A \ S)) (hBa : stouches a B)
    (hCAS : C ∈ components (A \ S)) (hCa : stouches a C) : B = C :=
  unique_mem_cmpnts_diff_surface_wtouches_of_center_mem_IsOpen ha hA hcA
    hBAS (wtouches_of_stouches ha hBa)
    hCAS (wtouches_of_stouches ha hCa)


theorem touches_iff_forall_wtouches (ha : ESide S a) {b : ℕ → Set X} (hb : ESide S b) :
    touches a b ↔ ∀ n, wtouches a (b n) :=
  Iff.intro
    (fun h n m => match h (Nat.max n m) with
      | ⟨p, hp⟩ => ⟨p, ⟨
        nested ha (Nat.le_max_right n m) hp.1,
        nested hb (Nat.le_max_left n m) hp.2⟩⟩)
    (fun h n => h n n)


theorem center_eq_of_touches [hXT2 : T2Space X] (ha : ESide S a) {b : ℕ → Set X}
    (hb : ESide S b) (hab : touches a b) : center ha = center hb :=
  Classical.byContradiction (fun hCenterNeq => match hXT2.t2 hCenterNeq with
  | ⟨_, _, hU, hV, haU, hbV, hUV⟩ => match stouches_of_center_mem_IsOpen ha hU haU with
  | ⟨k, hk⟩ => match stouches_of_center_mem_IsOpen hb hV hbV with
  | ⟨j, hj⟩ => match (touches_iff_forall_wtouches ha hb).mp hab j k with
  | ⟨_, hp⟩ => Set.disjoint_iff_forall_ne.mp hUV (hk hp.1) (hj hp.2) rfl)


theorem forall_wtouches_iff_forall_stouches [hXT2 : T2Space X]
  (ha : ESide S a) {b : ℕ → Set X} (hb : ESide S b) :
    (∀ n, wtouches a (b n)) ↔ (∀ n, stouches a (b n)) :=
  Iff.intro
    (fun hWeak n => Classical.byContradiction (fun hStrong =>
      match ha.exists_generator with
      | ⟨Ea, hEa⟩ => match hb.exists_generator with
      | ⟨Eb, hEb⟩ =>
      have hGenCenterEq : hEa.isEncapsulation.center = hEb.isEncapsulation.center := by
        rw [← center_eq_generator_center ha hEa, ← center_eq_generator_center hb hEb]
        exact center_eq_of_touches ha hb
          ((touches_iff_forall_wtouches ha hb).mpr hWeak)
      match (hEa.isEncapsulation.exists_subset_of_center_mem_IsOpen
        (hEb.isEncapsulation.nth_IsOpen n)
        (hGenCenterEq ▸ hEb.isEncapsulation.center_mem_nth n)) with
      | ⟨k, hk⟩ => match Set.not_subset.mp (not_exists.mp hStrong k) with
      | ⟨p, hp⟩ => hp.2 (mem_cmpnts_maximal (hEb.nth_mem_cmpnts n) (ha.nth_isPreconnected k)
        (fun p hp => ⟨hk (nth_subset_generator hEa k hp), not_mem_surface_of_mem_nth ha hp⟩)
        (hWeak n k) hp.1)))
    (fun h n => wtouches_of_stouches ha (h n))


theorem touches_iff_forall_stouches [hXT2 : T2Space X] (ha : ESide S a)
    {b : ℕ → Set X} (hb : ESide S b) : touches a b ↔ ∀ n, stouches a (b n) :=
  Iff.trans
    (touches_iff_forall_wtouches ha hb)
    (forall_wtouches_iff_forall_stouches ha hb)


theorem touches_refl (ha : ESide S a) : touches a a :=
  fun n => match nth_nonempty ha n with | ⟨p, hp⟩ => ⟨p, hp, hp⟩


omit hX in theorem touches_symm {b : ℕ → Set X} (hab : touches a b) :
    touches b a :=
  fun n => match hab n with | ⟨p, hpa, hpb⟩ => ⟨p, hpb, hpa⟩


theorem touches_trans [hXT2 : T2Space X] (ha : ESide S a) {b : ℕ → Set X} (hb : ESide S b)
    {c : ℕ → Set X} (hc : ESide S c) (hab : touches a b) (hbc : touches b c) : touches a c :=
  fun n => inter_nonempty_of_stouches hb
    ((touches_iff_forall_stouches hb ha).mp (touches_symm hab) n)
    ((touches_iff_forall_stouches hb hc).mp hbc n)


theorem touches_subsequence (ha : ESide S a) {α : ℕ → ℕ}
    (hαStrictMono : StrictMono α) : touches a (a ∘ α) :=
  fun n => match nth_nonempty ha (α n) with
  | ⟨p, hp⟩ => ⟨p, nested ha (hαStrictMono.id_le n) hp, hp⟩


theorem stouches_of_touches_of_stouches [hXT2 : T2Space X] (ha : ESide S a) {b : ℕ → Set X}
  (hb : ESide S b) (hab : touches a b) {A : Set X} (haA : stouches a A) :
    stouches b A :=
  match haA with
  | ⟨n, hn⟩ => match (touches_iff_forall_stouches hb ha).mp (touches_symm hab) n with
  | ⟨k, hk⟩ => ⟨k, subset_trans hk hn⟩


theorem eq_of_touches {b : ℕ → Set X} (hab : touches a b) {E : ℕ → Set X}
    (hEa : IsGenerator S a E) (hEb : IsGenerator S b E) : a = b :=
  funext fun n => (mem_cmpnts_eq_iff_inter_nonempty
    (hEa.nth_mem_cmpnts n) (hEb.nth_mem_cmpnts n)).mpr (hab n)


lemma _helper (ha : ESide S a) {E E' : ℕ → Set X} (hE : IsGenerator S a E)
  (hE' : Encapsulation E') (hEE' : hE.isEncapsulation.center = hE'.center) :
    ∀ (n : ℕ), stouches a (E' n) :=
  fun n => stouches_of_center_mem_IsOpen ha (hE'.nth_IsOpen n)
    (center_eq_generator_center ha hE ▸ hEE' ▸ hE'.center_mem_nth n)


lemma _helper2 (ha : ESide S a) {E E' : ℕ → Set X} (hE : IsGenerator S a E)
  (hE' : Encapsulation E') (hEE' : hE.isEncapsulation.center = hE'.center) :
    ∀ n, ∀ C ∈ components (E' n \ S), (∃ k, a k ⊆ C) →
    ∃ D ∈ components (E' (n + 1) \ S), (∃ k, a k ⊆ D) ∧ D ⊆ C :=
  fun n _ hC ⟨k, hk⟩ => match _helper ha hE hE' hEE' (n + 1) with
  | ⟨j, hj⟩ =>
  have hakj := (fun _ hp =>
    ⟨hj (nested ha (Nat.le_max_right k j) hp), not_mem_surface_of_mem_nth ha hp⟩)
  match exists_subset_mem_cmpnts_of_subset hakj (nth_isConnected ha _) with
  | ⟨D, hD⟩ => ⟨D, hD.1, ⟨Nat.max k j, hD.2⟩,
    mem_cmpnts_maximal hC (isPreconnected_mem_cmpnts hD.1)
      (fun _ hp => ⟨hE'.nested (Nat.le_succ n) (mem_cmpnts_subset hD.1 hp).1,
        (mem_cmpnts_subset hD.1 hp).2⟩)
      (match nth_nonempty ha (Nat.max k j) with
        | ⟨p, hp⟩ => ⟨p, hD.2 hp, hk (nested ha (Nat.le_max_left k j) hp)⟩)⟩


def _recursive_map (ha : ESide S a) {E E' : ℕ → Set X} (hE : IsGenerator S a E)
  (hE' : Encapsulation E') (hEE' : hE.isEncapsulation.center = hE'.center) (m : ℕ) :
    Σ' (C : Set X), C ∈ components (E' m \ S) ∧ (∃ k, a k ⊆ C) :=
  match m with
  | 0 =>
    let i := Classical.choose (_helper ha hE hE' hEE' 0)
    have hi := Classical.choose_spec (_helper ha hE hE' hEE' 0)
    have hak : a i ⊆ E' 0 \ S := fun _ hp => ⟨hi hp, not_mem_surface_of_mem_nth ha hp⟩
    have hC := exists_subset_mem_cmpnts_of_subset hak (nth_isConnected ha i)
    have hCSpec := Classical.choose_spec hC
    ⟨Classical.choose hC, hCSpec.1, i, hCSpec.2⟩
  | n + 1 =>
    ⟨Classical.choose (_helper2 ha hE hE' hEE' n
      (_recursive_map ha hE hE' hEE' n).1
      (_recursive_map ha hE hE' hEE' n).2.1
      (_recursive_map ha hE hE' hEE' n).2.2),
    (Classical.choose_spec (_helper2 ha hE hE' hEE' n
      (_recursive_map ha hE hE' hEE' n).1
      (_recursive_map ha hE hE' hEE' n).2.1
      (_recursive_map ha hE hE' hEE' n).2.2)).1,
    (Classical.choose_spec (_helper2 ha hE hE' hEE' n
      (_recursive_map ha hE hE' hEE' n).1
      (_recursive_map ha hE hE' hEE' n).2.1
      (_recursive_map ha hE hE' hEE' n).2.2)).2.1⟩


theorem exists_reencapsulation [hXT2 : T2Space X] (ha : ESide S a)
  {E E' : ℕ → Set X} (hE : IsGenerator S a E) (hE' : Encapsulation E')
  (hEE' : hE.isEncapsulation.center = hE'.center) :
    ∃ a', ESide S a' ∧ IsGenerator S a' E' ∧ touches a a' :=

  have hE'b := IsGenerator.mk hE' fun n => (_recursive_map ha hE hE' hEE' n).2.1
  have hb : ESide S fun n => (_recursive_map ha hE hE' hEE' n).fst := by
    apply ESide.mk
    · exact ⟨E', hE'b⟩
    · intro n
      exact (Classical.choose_spec (
        _helper2 ha hE hE' hEE' n (_recursive_map ha hE hE' hEE' n).1
        (_recursive_map ha hE hE' hEE' n).2.1
        (_recursive_map ha hE hE' hEE' n).2.2)).2.2

  ⟨fun n => (_recursive_map ha hE hE' hEE' n).1, hb, hE'b, (touches_iff_forall_stouches ha hb).mpr
    fun n => (_recursive_map ha hE hE' hEE' n).2.2⟩



end ESide



theorem Encapsulation.isCenter_ESide_center (ha : ESide S a) {E} (hE : ESide.IsGenerator S a E) :
    Encapsulation.isCenter E (ESide.center ha) :=
  (ha.isCenter_iff_isCenter_generator hE ha.center).mp (ESide.isCenter_center ha)
