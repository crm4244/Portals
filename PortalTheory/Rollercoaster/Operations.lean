import PortalTheory.Rollercoaster.Basic
import PortalTheory.Rollercoaster.Trivial

namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}





section drop

variable {n : ℕ} (hn : n < R.points.length)


def drop : Rollercoaster 𝒰 (R.points[n]) b where
  points := R.points.drop n
  regions := R.regions.drop n
  len_rgs_add_one_eq_len_pts := by
    simp only [List.length_drop, R.len_rgs_add_one_eq_len_pts.symm]
    apply Nat.sub_add_comm (Nat.le_of_lt_succ <| by simp [R.len_rgs_add_one_eq_len_pts, hn]) |>.symm
  mem_rgs t := by
    simp only [Fin.getElem_fin, List.getElem_drop]
    exact R.mem_rgs ⟨n + t, Nat.add_lt_of_lt_sub' <| List.length_drop ▸ t.2⟩
  succ_mem_rgs t := by
    simp only [Fin.getElem_fin, List.getElem_drop]
    exact R.succ_mem_rgs ⟨n + t, Nat.add_lt_of_lt_sub' <| List.length_drop ▸ t.2⟩
  head_pts_eq := by simp
  getLast_pts_eq := by simp [R.getLast_pts_eq]


theorem drop_zero : R.drop (n := 0) R.len_pts_pos ≍ R := sorry




end drop


section take

variable {n : ℕ} (hn : n < R.points.length - 1)




def take : Rollercoaster 𝒰 a (R.points[n]) :=
  have h : R.points.take (n + 1) ≠ [] :=
    (not_or_intro (Nat.not_succ_le_zero n ·.le) R.pts_ne_nil <| List.take_eq_nil_iff.mp ·)
  {
    points := R.points.take (n + 1)
    regions := R.regions.take n
    len_rgs_add_one_eq_len_pts := by
      rw [List.length_take_of_le <| R.len_rgs_eq_len_pts_sub_one ▸ hn.le]
      rw [List.length_take_of_le <| le_of_eq_of_le'
        (Nat.sub_one_add_one_eq_of_pos R.len_pts_pos) <| Nat.succ_le_succ hn.le]
    mem_rgs t := by
      simp only [Fin.getElem_fin, List.getElem_take]
      exact R.mem_rgs ⟨t.1, lt_of_le_of_lt' (min_le_right _ _) <|
        lt_of_eq_of_lt' List.length_take t.2⟩
    succ_mem_rgs t := by
      simp only [Fin.getElem_fin, List.getElem_take]
      exact R.succ_mem_rgs ⟨t.1, lt_of_le_of_lt' (min_le_right _ _) <|
        lt_of_eq_of_lt' List.length_take t.2⟩
    head_pts_eq := List.head_take h |>.trans R.head_pts_eq
    getLast_pts_eq := List.getLast_take h |>.trans <| Option.getD_eq_iff.mpr <|
      Or.inl <| getElem?_eq_some_getElem_iff _ |>.mpr True.intro
  }


/-
def take : Rollercoaster 𝒰 a (R.points[n - 1]) :=
  have h_take_nonempty : R.points.take n ≠ [] := List.ne_nil_of_length_pos <|
    List.length_take ▸ lt_inf_iff.mpr ⟨hpos, R.len_pts_pos⟩
  {
    points := R.points.take n
    regions := R.regions.take (n - 1)
    len_rgs_add_one_eq_len_pts := by
      have h : n - 1 ≤ R.regions.length :=
        le_of_eq_of_le' R.len_rgs_eq_len_pts_sub_one.symm <| Nat.sub_le_sub_right hn.le 1
      rw [List.length_take_of_le hn.le, List.length_take_of_le h]
      exact Nat.sub_one_add_one_eq_of_pos hpos
    mem_rgs t := by
      simp only [Fin.getElem_fin, List.getElem_take]
      exact R.mem_rgs ⟨t.1, lt_of_le_of_lt' (min_le_right _ _) <|
        lt_of_eq_of_lt' List.length_take t.2⟩
    succ_mem_rgs t := by
      simp only [Fin.getElem_fin, List.getElem_take]
      exact R.succ_mem_rgs ⟨t.1, lt_of_le_of_lt' (min_le_right _ _) <|
        lt_of_eq_of_lt' List.length_take t.2⟩
    head_pts_eq := List.head_take h_take_nonempty |>.trans R.head_pts_eq
    getLast_pts_eq := List.getLast_take h_take_nonempty |>.trans <|
      Option.getD_eq_iff.mpr <| Or.inl <| getElem?_eq_some_getElem_iff _ |>.mpr True.intro
  }
-/



@[simp] theorem len_pts_take : (R.take hn).points.length = n + 1 :=
  List.length_take.trans <| inf_eq_left.mpr <| Nat.add_lt_of_lt_sub hn |>.le


@[simp] theorem len_rgs_take : (R.take hn).regions.length = n := by
  sorry


end take






--theorem len_regions_eq_len_tail_points : R.regions.length = R.points.tail.length :=
  --R.length_regions_eq.trans R.points.length_tail.symm


--theorem tail_points_ne_nil_of_len_regions_pos (h : 0 < R.regions.length) : R.points.tail ≠ [] :=
  --R.points.tail.ne_nil_of_length_pos <| R.len_regions_eq_len_tail_points ▸ h


/-
def tail (h_nontrivial : 0 < R.regions.length) :
  Rollercoaster 𝒰 (R.points.tail.head <| tail_points_ne_nil_of_len_regions_pos h_nontrivial) b :=

  let fin_tail_regl_to_succ (n : Fin R.regions.tail.length) : Fin R.regions.length :=
    ⟨n + 1, R.regions.length_tail_add_one h_nontrivial ▸ Nat.succ_lt_succ n.isLt⟩
  {
    points := R.points.tail
    regions := R.regions.tail
    h_length := R.regions.length_tail_add_one h_nontrivial |>.trans R.len_regions_eq_len_tail_points
    head_eq := rfl
    last_eq := List.getLast_tail _ |>.trans R.last_eq
    mem_region n := by
      simp only [Fin.getElem_fin, List.getElem_tail]
      exact R.mem_region <| fin_tail_regl_to_succ n
    next_mem_region n := by
      simp only [Fin.getElem_fin, List.getElem_tail]
      exact R.next_mem_region <| fin_tail_regl_to_succ n
  }
-/

/-
def dropLast (h_nontrivial : 0 < R.regions.length) :
  Rollercoaster 𝒰 a <| R.points.getLast R.points_ne_nil where
    points := R.points.dropLast
    regions := R.regions.dropLast
    h_length := by sorry
    head_eq := by
      apply List.head_dropLast (by
        apply List.ne_nil_iff_length_pos.mpr

        rw [List.length_dropLast]

        sorry) |>.trans R.head_eq
    last_eq := by sorry
    mem_region := by sorry
    next_mem_region := by sorry
-/


/-
section extract

def extract {start stop : Fin R.points.length} (hlt : start < stop) :
  Rollercoaster 𝒰 R.points[start] R.points[stop] where
    points := R.points.extract start stop
    regions := R.regions.extract start stop
    h_length := by sorry
    head_eq :=
      have h_drop_start_ne_nil : R.points.drop start ≠ [] :=
        (not_le_of_gt start.isLt <| List.drop_eq_nil_iff.mp ·)
      by exact (List.head_take
        (fun h ↦ not_or_intro (not_le_of_gt hlt <| Nat.le_of_sub_eq_zero ·)
          h_drop_start_ne_nil (List.take_eq_nil_iff.mp h)
        )).trans <| (List.head_drop h_drop_start_ne_nil).trans rfl
    last_eq := by sorry
    mem_region := by sorry
    next_mem_region := by sorry

end extract
-/










section map

variable {β : Type*} {m : α → β} {𝒰' : Set (Set β)}
variable (h : ∀ A : 𝒰, ∃ A' ∈ 𝒰', m '' A ⊆ A')


open Classical in noncomputable def map : Rollercoaster 𝒰' (m a) (m b) where
  points := R.points.map m
  regions := R.regions.map fun A : 𝒰 ↦ ⟨choose (h A), choose_spec (h A) |>.1⟩
  len_rgs_add_one_eq_len_pts := by simp only [List.length_map, R.len_rgs_add_one_eq_len_pts]
  head_pts_eq := by simp [R.head_pts_eq]
  getLast_pts_eq := by simp [R.getLast_pts_eq]
  mem_rgs := fun ⟨n, hn⟩ ↦ by
    simp only [List.length_map] at hn
    simp only [Fin.getElem_fin, List.getElem_map]
    exact (choose_spec <| h <| R.regions[n]).2
      ⟨R.points[n]' (hn.trans R.len_rgs_lt_len_pts), R.mem_rgs ⟨n, hn⟩, rfl⟩
  succ_mem_rgs := fun ⟨n, hn⟩ ↦ by
    simp only [List.length_map] at hn
    simp only [Fin.getElem_fin, List.getElem_map]
    exact (choose_spec <| h <| R.regions[n]).2
      ⟨R.points[n + 1]' (by simp [← R.len_rgs_add_one_eq_len_pts, hn]), R.succ_mem_rgs ⟨n, hn⟩, rfl⟩


@[simp] theorem length_map : (R.map h).points.length = R.points.length :=
  List.length_map _


theorem len_rgs_map : (R.map h).regions.length = R.regions.length := sorry


@[simp] theorem getElem_pts_map (n : Fin (R.map h).points.length) :
  (R.map h).points[n] = m (R.points[n]' (R.length_map h ▸ n.2)) :=
    List.getElem_map _



@[simp] theorem getElem_rgs_map (n : Fin (R.map h).regions.length) :
  m '' (R.regions[n]'(R.len_rgs_map h ▸ n.2)) ⊆ (R.map h).regions[n] := by
    simp_all only [Fin.getElem_fin]
    simp only [map, List.getElem_map]
    exact Classical.choose_spec (h <| R.regions[n]'_) |>.2





end map





section append

variable {c : α} (R) (R' : Rollercoaster 𝒰 b c)



-- we can make this nicer
def append : Rollercoaster 𝒰 a c where

  points := R.points ++ R'.points.tail
  regions := R.regions ++ R'.regions
  len_rgs_add_one_eq_len_pts := by
    simp [← R.len_rgs_add_one_eq_len_pts, ← R'.len_rgs_add_one_eq_len_pts]; grind
  head_pts_eq := by
    simp only [List.head_append, dif_neg <| List.isEmpty_iff.ne.mpr R.pts_ne_nil, head_pts_eq]
  getLast_pts_eq := by
    simp [List.getLast_append, List.getLast_tail, R'.getLast_pts_eq, R.getLast_pts_eq]
    intro h
    simp only [List.eq_nil_iff_length_eq_zero, List.length_tail,
      ← R'.len_rgs_eq_len_pts_sub_one] at h
    exact R'.last_eq_head_of_isTrivial (len_rgs_eq_zero_iff_isTrivial.mp h) |>.symm
  mem_rgs := fun ⟨n, hn⟩ ↦ by
    simp [List.getElem_append, ← R.len_rgs_add_one_eq_len_pts] at ⊢ hn
    rcases lt_trichotomy n R.regions.length with hlt | heq | hgt
    · simp only [dif_pos hlt, dif_pos <| Nat.lt_succ_of_lt hlt]
      exact R.mem_rgs ⟨n, hlt⟩
    · simp [heq, -getElem_len_rgs] at ⊢ hn
      exact R.getElem_len_rgs.trans R'.getElem_zero.symm ▸
        R'.mem_rgs ⟨0, R'.len_rgs_pos_iff_not_isTrivial.mpr hn⟩
    · simp only [dif_neg <| not_lt.mpr <| Nat.succ_le_of_lt hgt,
        dif_neg <| not_lt_of_gt hgt, Nat.sub_add_eq,
        (Nat.sub_add_cancel <| Nat.one_le_iff_ne_zero.mpr <| Nat.sub_ne_zero_of_lt hgt)]
      exact R'.mem_rgs ⟨_, Nat.sub_lt_left_of_lt_add (le_of_lt hgt) hn⟩
  succ_mem_rgs := fun ⟨n, hn⟩ ↦ by
    simp [List.getElem_append, ← R.len_rgs_add_one_eq_len_pts] at ⊢ hn
    rcases lt_trichotomy n R.regions.length with hlt | heq | hgt
    · simp only [dif_pos hlt]; exact R.succ_mem_rgs ⟨n, hlt⟩
    · simp [heq] at ⊢ hn; exact R'.succ_mem_rgs ⟨0, R'.len_rgs_pos_iff_not_isTrivial.mpr hn⟩
    · simp only [dif_neg (not_lt_of_gt hgt)]
      exact R'.succ_mem_rgs ⟨_, Nat.sub_lt_left_of_lt_add (le_of_lt hgt) hn⟩


instance : HAppend (Rollercoaster 𝒰 a b) (Rollercoaster 𝒰 b c) (Rollercoaster 𝒰 a c) :=
  ⟨(append · ·)⟩


@[simp] theorem length_pts_append :
  (R ++ R').points.length = R.points.length + R'.points.length - 1 :=
    List.length_append.trans <| List.length_tail ▸ Nat.add_sub_assoc
      (Nat.one_le_of_lt R'.len_pts_pos) _ |>.symm


@[simp] theorem getElem_pts_append_left {i : ℕ} (h : i < R.points.length)
  {h' : i < (R ++ R').points.length} :
    (R ++ R').points[i] = R.points[i] :=
  (List.getElem_append_left h).trans rfl


@[simp] theorem getElem_pts_append_right {i : ℕ} (h₁ : R.points.length - 1 ≤ i)
  {h₂ : i < (R ++ R').points.length} :
    (R ++ R').points[i] = R'.points[i + 1 - R.points.length]'(Nat.sub_lt_left_of_lt_add
      (Nat.le_succ_of_pred_le h₁) <| Nat.succ_lt_of_lt_pred <|
        lt_of_eq_of_lt' (R.length_pts_append R') h₂) := by
  apply Or.by_cases h₁.eq_or_lt
  · intro h
    apply List.getElem_append_left (lt_of_eq_of_lt h.symm <| Nat.pred_lt R.len_pts_ne_zero) |>.trans
    simp [h.symm, Nat.sub_one_add_one R.len_pts_ne_zero]
  · intro h
    have h' : R.points.length ≤ i := Nat.le_of_pred_lt h
    exact List.getElem_append_right h' |>.trans <| (List.getElem_tail _).trans <|
      congr_arg R'.points.get <| Fin.mk_eq_mk.mpr <| Nat.sub_add_comm h' |>.symm



end append




end Rollercoaster
