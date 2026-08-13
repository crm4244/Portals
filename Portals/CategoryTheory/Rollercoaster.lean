--import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UnitInterval

open Topology TopologicalSpace

variable {α : Type*}



structure Rollercoaster (𝒰 : Set (Set α)) (a b : α) where
  points : List α
  regions : List 𝒰

  h_length : regions.length + 1 = points.length
  points_neq_nil : points ≠ [] := List.ne_nil_of_length_eq_add_one h_length.symm

  mem_region : ∀ n : Fin regions.length, points[n] ∈ regions[n].1
  next_mem_region : ∀ n : Fin regions.length, points[n.succ] ∈ regions[n].1

  head_eq : points.head points_neq_nil = a
  last_eq : points.getLast points_neq_nil = b



namespace Rollercoaster

variable {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



theorem len_regions_lt_len_points : R.regions.length < R.points.length :=
  R.h_length ▸ Nat.lt_add_one _

theorem len_points_neq_zero : R.points.length ≠ 0 :=
  R.h_length ▸ by aesop

theorem not_points_isEmpty : ¬R.points.isEmpty :=
  (R.points_neq_nil <| List.isEmpty_iff.mp ·)

theorem len_points_pos : 0 < R.points.length :=
  R.h_length ▸ Nat.zero_lt_succ _


theorem getElem_regions_eq :
  R.points[R.regions.length]'R.len_regions_lt_len_points = b := by
    simp [← R.last_eq, List.getLast_eq_getElem, ← R.h_length]



theorem head_eq_last (h : R.regions.length = 0) : a = b := by
  simp [← R.head_eq, List.head_eq_getElem, ← R.last_eq, List.getLast_eq_getElem, ← R.h_length, h]


def of_pair {U : 𝒰} {p q : α} (hp : p ∈ U.1) (hq : q ∈ U.1) : Rollercoaster 𝒰 p q where
  points := [p, q]
  regions := [U]
  h_length := by simp
  head_eq := rfl
  last_eq := rfl
  mem_region := by simp [hp]
  next_mem_region := by simp [hq]




section jumps

variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)


def jump (n : Fin R.regions.length) := @f R.regions[n]
  ⟨R.points[n]' (R.h_length ▸ Nat.lt_succ_of_lt n.2), R.mem_region n⟩
  ⟨R.points[n.succ]' (R.h_length ▸ Nat.succ_lt_succ n.2), R.next_mem_region n⟩


def jumpTo : (n : Fin R.points.length) → T a → T R.points[n]
  | ⟨0, _⟩ => cast <| congr_arg T <|
    R.head_eq.symm.trans <| List.head_eq_getElem R.points_neq_nil
  | ⟨n + 1, h⟩ => R.jump f ⟨n, Nat.add_one_lt_add_one_iff.mp <| R.h_length.symm ▸ h⟩ ∘
    jumpTo ⟨n, Nat.lt_succ_self n |>.trans h⟩


def jumpAll : T a → T b := fun a ↦
  cast (congr_arg T <| List.getLast_eq_getElem R.points_neq_nil |>.symm.trans R.last_eq) <|
    R.jumpTo f ⟨R.points.length - 1, Nat.sub_one_lt R.len_points_neq_zero⟩ a


end jumps





section map

variable {β : Type*} {m : α → β} {𝒰' : Set (Set β)}
variable (h : ∀ A : 𝒰, ∃ A' ∈ 𝒰', m '' A ⊆ A')


open Classical in noncomputable def map : Rollercoaster 𝒰' (m a) (m b) where
  points := R.points.map m
  regions := R.regions.map fun A : 𝒰 ↦ ⟨choose (h A), choose_spec (h A) |>.1⟩
  h_length := by simp only [List.length_map, R.h_length]
  head_eq := by simp [R.head_eq]
  last_eq := by simp [R.last_eq]
  mem_region := fun ⟨n, hn⟩ ↦ by
    simp only [List.length_map] at hn
    simp only [Fin.getElem_fin, List.getElem_map]
    exact (choose_spec <| h <| R.regions[n]).2
      ⟨R.points[n]' (by simp [← R.h_length, Nat.lt_succ_of_lt hn]), R.mem_region ⟨n, hn⟩, rfl⟩
  next_mem_region := fun ⟨n, hn⟩ ↦ by
    simp only [List.length_map] at hn
    simp only [Fin.getElem_fin, List.getElem_map]
    exact (choose_spec <| h <| R.regions[n]).2
      ⟨R.points[n + 1]' (by simp [← R.h_length, hn]), R.next_mem_region ⟨n, hn⟩, rfl⟩


theorem length_map : (R.map h).points.length = R.points.length :=
  List.length_map _


theorem getElem_map (n : Fin (R.map h).points.length) :
  (R.map h).points[n] = m (R.points[n]' (R.length_map h ▸ n.2)) :=
    List.getElem_map _



variable {T : β → Type*}
variable (f : {U : 𝒰'} → (p : U.1) → (q : U.1) → T p.1 → T q.1)

open Classical in theorem jumpAll_map_apply (x : T (m a)) :
  (R.map h).jumpAll (T := T) f x = R.jumpAll (T := T ∘ m)
    (fun {U} ⟨p, hp⟩ ⟨q, hq⟩ ↦ let hU := choose_spec (h U)
      @f ⟨choose (h U), hU.1⟩ ⟨m p, hU.2 ⟨p, hp, rfl⟩⟩ ⟨m q, hU.2 ⟨q, hq, rfl⟩⟩) x := by

/-
  induction h_ind : R.regions.length
  · unfold jumpAll

    --unfold jumpTo

    apply cast_eq_iff_heq.mpr _
    symm
    apply HEq.congr_simp (cast _ x) (cast _ x) (by
      sorry) _ _ (by
      have hrw : ⟨R.points.length - 1, Nat.sub_one_lt R.len_points_neq_zero⟩ =
        (⟨0, R.len_points_pos⟩ : Fin R.points.length) := by
        simp only [R.h_length.symm.trans <| Nat.succ_inj.mpr h_ind]
      rw [hrw]
      unfold jumpTo
      rw [R.h_length.symm.trans <| Nat.succ_inj.mpr h_ind]

      sorry) |>.mpr

    #check R.h_length.symm.trans <| Nat.succ_inj.mpr h_ind

    simp?






    sorry
-/
  sorry

end map





section append
variable {c : α} (R' : Rollercoaster 𝒰 b c)

-- we can make this nicer
def append : Rollercoaster 𝒰 a c where

  points := R.points ++ R'.points.tail
  regions := R.regions ++ R'.regions
  h_length := by simp [← R.h_length, ← R'.h_length]; grind
  head_eq := by simp only [List.head_append, dif_neg not_points_isEmpty, head_eq]
  last_eq := by
    simp only [List.getLast_append, List.getLast_tail, R'.last_eq, R.last_eq]
    exact dite_eq_right_iff.mpr fun h ↦ R'.head_eq_last <| by
      simp only [List.isEmpty_iff, List.eq_nil_iff_length_eq_zero,
        List.length_tail, ← R'.h_length] at h
      exact h

  mem_region := fun ⟨n, hn⟩ ↦ by
    simp [List.getElem_append, ← R.h_length] at ⊢ hn
    rcases lt_trichotomy n R.regions.length with hlt | heq | hgt
    · simp only [dif_pos hlt, dif_pos (Nat.lt_succ_of_lt hlt)]
      exact R.mem_region ⟨n, hlt⟩
    · simp [heq, getElem_regions_eq, ← R'.head_eq, List.head_eq_getElem] at ⊢ hn
      exact R'.mem_region ⟨0, hn⟩
    · simp only [dif_neg <| not_lt.mpr <| Nat.succ_le_of_lt hgt,
        dif_neg <| not_lt_of_gt hgt, Nat.sub_add_eq,
        (Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.mpr <| Nat.sub_ne_zero_of_lt hgt)]
      exact R'.mem_region ⟨_, Nat.sub_lt_left_of_lt_add (le_of_lt hgt) hn⟩
  next_mem_region := fun ⟨n, hn⟩ ↦ by
    simp [List.getElem_append, ← R.h_length] at ⊢ hn
    rcases lt_trichotomy n R.regions.length with hlt | heq | hgt
    · simp only [dif_pos hlt]; exact R.next_mem_region ⟨n, hlt⟩
    · simp [heq] at ⊢ hn; exact R'.next_mem_region ⟨0, hn⟩
    · simp only [dif_neg (not_lt_of_gt hgt)]
      exact R'.next_mem_region ⟨_, Nat.sub_lt_left_of_lt_add (le_of_lt hgt) hn⟩


variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)


theorem jumpAll_append_apply {c : α} (R' : Rollercoaster 𝒰 b c) (x : T a) :
  (R.append R').jumpAll f x = R'.jumpAll f (R.jumpAll f x) := by

  sorry


theorem jumpAll_append {c : α} {R' : Rollercoaster 𝒰 b c} :
  (R.append R').jumpAll f = R'.jumpAll f ∘ R.jumpAll f :=
    funext fun _ ↦ jumpAll_append_apply _ _ _


end append




theorem nonempty_of_finite_preorder_from [Finite 𝒰] {preorder : Preorder 𝒰} {endpoint : α}
  (endPoint_mem_region_of_minimal : ∀ U : 𝒰, @Minimal 𝒰 preorder.toLE Set.univ U → endpoint ∈ U.1)
  (exists_lt_of_not_minimal : ∀ U : 𝒰, ¬@Minimal 𝒰 preorder.toLE Set.univ U →
    ∃ x ∈ U.1, ∃ V : 𝒰, x ∈ V.1 ∧ preorder.lt V U) :
      ∀ U : 𝒰, ∀ x ∈ U.1, Nonempty (Rollercoaster 𝒰 x endpoint) :=
  fun U' ↦ @Finite.to_wellFoundedLT.induction 𝒰 preorder.toLT
    (fun U ↦ ∀ x ∈ U.1, Nonempty (Rollercoaster 𝒰 x endpoint)) U'
    (fun U h_ind _ hx ↦ by_cases
      (fun h_minimal : @Minimal 𝒰 preorder.toLE Set.univ U ↦
        Nonempty.intro <| of_pair hx <| endPoint_mem_region_of_minimal U h_minimal)
      (fun h_minimal : ¬@Minimal 𝒰 preorder.toLE Set.univ U ↦
        let ⟨y, hyU, V, hyV, hVU⟩ := exists_lt_of_not_minimal U h_minimal
        Nonempty.intro <| (of_pair hx hyU).append <| Classical.choice <| h_ind V hVU y hyV))


theorem nonempty_bot_to_top [TopologicalSpace α] [CompleteLinearOrder α]
  [DenselyOrdered α] [OrderTopology α] [CompactSpace α]
  (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ x : α, ∃ U ∈ 𝒰, x ∈ U) :
    Nonempty (Rollercoaster 𝒰 ⊥ ⊤) := by

  let supOrder : Preorder (Set α) := {
    le A B := ∀ b ∈ B, ∃ a ∈ A, b ≤ a
    le_refl _ := fun a h ↦ ⟨a, h, le_rfl⟩
    le_trans _ _ _ hAB hBC := fun a ha ↦
      let ⟨b, hb, hab⟩ := hBC a ha
      let ⟨c, hc, hbc⟩ := hAB b hb
      ⟨c, hc, hab.trans hbc⟩
    lt A B := ∃ a ∈ A, ∀ b ∈ B, b < a
    lt_iff_le_not_ge A B := ⟨
      fun ⟨a, ha, hB⟩ ↦ ⟨
        fun b hb ↦ ⟨a, ha, le_of_lt <| hB b hb⟩,
        fun hA ↦ let ⟨b', hb', hle⟩ := hA a ha; not_lt_of_ge hle <| hB b' hb'⟩,
      fun ⟨_, h⟩ ↦ by simp at h; exact h⟩}

  obtain ⟨t, t_cover⟩ := ‹CompactSpace α›.isCompact_univ.elim_finite_subcover
    (@Subtype.val _ {U | U ∈ 𝒰 ∧ Nonempty U}) (fun ⟨U, hU, _⟩ ↦ h_open ⟨U, hU⟩)
      (fun x _ ↦ let ⟨U, hU, hx⟩ := h_cover x; ⟨U, ⟨⟨U, hU, Nonempty.intro ⟨x, hx⟩⟩, rfl⟩, hx⟩)
  let t_set : Set (Set α) := Subtype.val '' SetLike.coe t

  have top_mem_iff_minimal_t : ∀ U : t_set,
    @Minimal t_set (supOrder.lift Subtype.val).toLE Set.univ U ↔ ⊤ ∈ U.1 :=
    fun ⟨_, ⟨U, hU, rfl⟩⟩ ↦
      ⟨fun ⟨_, h_minimal⟩ ↦
        let ⟨_, ⟨V, rfl⟩, _, ⟨hV, rfl⟩, htopV⟩ := t_cover (Set.mem_univ ⊤)
        let V_t : t_set := ⟨V, V, hV, rfl⟩
        let ⟨_, ha, hle⟩ := @h_minimal V_t (Set.mem_univ V_t)
          (fun _ _ ↦ ⟨⊤, htopV, le_top⟩) ⊤ htopV
        top_le_iff.mp hle |>.symm ▸ ha,
      fun top_mem ↦ ⟨Set.mem_univ U, fun _ _ _ _ _ ↦ ⟨⊤, top_mem, le_top⟩⟩⟩

  have exists_lt_of_not_minimal_t : ∀ U : t_set,
    ¬@Minimal t_set (supOrder.lift Subtype.val).toLE Set.univ U →
      ∃ x ∈ U.1, ∃ V, x ∈ V.1 ∧ (supOrder.lift Subtype.val).lt V U :=
    fun ⟨_, U, hU, rfl⟩ h_minimal ↦
      let ⟨⟨V, hV, hV_nonempty⟩, _, ⟨hVt, rfl⟩, hsup⟩ :=
        Set.mem_iUnion.mp <| t_cover <| Set.mem_univ <| sSup U
      have h_le_of_mem : ∀ x ∈ U.1, x < sSup U :=
        fun _ hmem ↦ lt_iff_le_and_ne.mpr ⟨le_sSup hmem,
          fun heq ↦ not_congr (top_mem_iff_minimal_t <| _) |>.mp h_minimal
            ((top_le_iff.mp <| @le_of_not_gt _ _ ⊤ (sSup U.1)
              (fun h_sSup_lt_top ↦
                let ⟨x, hx, hico⟩ := exists_Ico_subset_of_mem_nhds
                  (IsOpen.mem_nhds (h_open ⟨U, U.2.1⟩) (heq ▸ hmem)) ⟨⊤, h_sSup_lt_top⟩
                let ⟨y, hygt, hylt⟩ := DenselyOrdered.dense _ _ hx
                lt_iff_not_ge.mp hygt <| le_sSup <| hico <| Set.mem_Ico.mpr ⟨hygt.le, hylt⟩))
              ▸ heq ▸ hmem)⟩
      let ⟨_, hl, hlioc⟩ := exists_Ioc_subset_of_mem_nhds (IsOpen.mem_nhds (h_open ⟨V, hV⟩) hsup)
        ⟨_, h_le_of_mem _ (Classical.choice U.2.2).2⟩
      let ⟨x, hx, hxl⟩ := lt_sSup_iff.mp hl
      ⟨x, hx, ⟨V, ⟨V, hV, hV_nonempty⟩, hVt, rfl⟩,
        hlioc <| Set.mem_Ioc.mpr ⟨hxl, le_sSup hx⟩, sSup U, hsup, h_le_of_mem⟩

  obtain ⟨_, ⟨U, rfl⟩, _, ⟨hU, rfl⟩, h_bot⟩ := t_cover <| Set.mem_univ ⊥
  obtain R' := Classical.choice <|
    @nonempty_of_finite_preorder_from α t_set _ (supOrder.lift Subtype.val)
    ⊤ (top_mem_iff_minimal_t · |>.mp) exists_lt_of_not_minimal_t ⟨U, U, hU, rfl⟩ ⊥ h_bot
  exact Nonempty.intro <| R'.map (m := id)
    (fun ⟨_, ⟨⟨U, hU, _⟩, _, rfl⟩⟩ ↦ ⟨U, hU, fun _ ⟨_, h, rfl⟩ ↦ h⟩)



open unitInterval in theorem nonempty_of_path [TopologicalSpace α]
  (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ x : α, ∃ U ∈ 𝒰, x ∈ U)
  {f : I → α} (h_continuous : Continuous f)
    : Nonempty (Rollercoaster 𝒰 (f 0) (f 1)) :=
  Nonempty.intro <| @map I {f ⁻¹' U | U : 𝒰} 0 1
    (Classical.choice <| nonempty_bot_to_top
      (fun ⟨_, _, rfl⟩ ↦ h_continuous.isOpen_preimage _ <| h_open _)
      (fun x ↦ let ⟨U, hU, hx⟩ := h_cover <| f x; ⟨f ⁻¹' U, ⟨⟨U, hU⟩, rfl⟩, hx⟩))
    _ _ _ fun ⟨_, ⟨U, h⟩, rfl⟩ ↦ ⟨U, h, Set.image_subset_iff.mpr subset_rfl⟩










variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)



def rel (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1) :
  Rollercoaster 𝒰 a b → Rollercoaster 𝒰 a b → Prop :=
    fun R1 R2 ↦ R1.jumpAll f = R2.jumpAll f



variable (h_cover : ∀ a : α, ∃ U : 𝒰, a ∈ U.1)

variable {f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1}
variable (f_id : ∀ {U : 𝒰} (p : U.1), f p p = id)
variable (f_trans : ∀ {U : 𝒰} (p q r : U.1), f q r ∘ f p q = f p r)
variable (f_inter : ∀ {U V : 𝒰} {p q : α} (hpU : p ∈ U.1) (hpV : p ∈ V.1)
  (hqU : q ∈ U.1) (hqV : q ∈ V.1),
    f ⟨p, hpU⟩ ⟨q, hqU⟩ = f ⟨p, hpV⟩ ⟨q, hqV⟩)







end Rollercoaster
