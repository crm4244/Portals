import PortalTheory.Rollercoaster.Basic


namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



def trivial (𝒰 : Set (Set α)) (a : α) : Rollercoaster 𝒰 a a where
  points := [a]
  regions := []
  len_rgs_add_one_eq_len_pts := by simp
  mem_rgs := by simp
  succ_mem_rgs := by simp
  head_pts_eq := rfl
  getLast_pts_eq := rfl


@[simp] theorem rgs_trivial : (trivial 𝒰 a).regions = [] := rfl
@[simp] theorem len_rgs_trivial : (trivial 𝒰 a).regions.length = 0 := by simp
@[simp] theorem pts_trivial : (trivial 𝒰 a).points = [a] := rfl
@[simp] theorem len_pts_trivial : (trivial 𝒰 a).points.length = 1 := by simp


def isTrivial : Prop := R ≍ (trivial 𝒰 a)
theorem isTrivial_iff (R : Rollercoaster 𝒰 a a) : R.isTrivial ↔ R = trivial 𝒰 a := heq_iff_eq


theorem isTrivial_trivial : (trivial 𝒰 a).isTrivial := HEq.rfl
theorem trivial_heq_of_eq : a = b → trivial 𝒰 a ≍ trivial 𝒰 b := (congr_arg_heq _ ·)

@[simp] theorem last_eq_head_of_isTrivial (h : R.isTrivial) : b = a := sorry
@[simp] theorem getLast_pts_of_isTrivial (h : R.isTrivial) : R.points.getLast R.pts_ne_nil = a := sorry
@[simp] theorem getElem_len_pts_sub_one_of_isTrivial (h : R.isTrivial) : R.points[R.points.length - 1]'sorry = a := sorry
@[simp] theorem getElem_len_rgs_of_isTrivial (h : R.isTrivial) : R.points[R.regions.length]'R.len_rgs_lt_len_pts = a := sorry
theorem last_eq_getElem_zero_of_isTrivial (h : R.isTrivial) : b = R.points[0]'R.len_pts_pos := sorry
theorem last_eq_head_pts_of_isTrivial (h : R.isTrivial) : b = R.points.head R.pts_ne_nil := sorry


theorem pts_eq_singleton_of_isTrivial (h : R.isTrivial) : R.points = [a] := sorry

theorem isTrivial_of_pts_eq_singleton (h : R.points = [a]) : R.isTrivial := by sorry

@[simp] theorem pts_eq_singleton_iff_isTrivial : R.points = [a] ↔ R.isTrivial :=
  ⟨(isTrivial_of_pts_eq_singleton ·), (pts_eq_singleton_of_isTrivial ·)⟩

theorem len_pts_eq_one_of_isTrivial (h : R.isTrivial) : R.points.length = 1 :=
  by simp [R.pts_eq_singleton_of_isTrivial h]

theorem isTrivial_of_len_pts_eq_one (h : R.points.length = 1) : R.isTrivial :=
  let ⟨_, h'⟩ := List.length_eq_one_iff.mp h
  isTrivial_of_pts_eq_singleton <| by
    simp [h']; exact (List.eq_of_mem_singleton <| h'.symm ▸ R.head_mem_pts).symm

@[simp] theorem len_pts_eq_one_iff_isTrivial : R.points.length = 1 ↔ R.isTrivial :=
  ⟨(isTrivial_of_len_pts_eq_one ·), (len_pts_eq_one_of_isTrivial ·)⟩

theorem len_pts_sub_one_eq_zero_of_isTrivial (h : R.isTrivial) : R.points.length - 1 = 0 :=
  by simp [R.pts_eq_singleton_of_isTrivial h]

theorem isTrivial_of_len_pts_sub_one_eq_zero (h : R.points.length - 1 = 0) : R.isTrivial := sorry

@[simp] theorem len_pts_sub_one_eq_zero_iff_isTrivial : R.points.length - 1 = 0 ↔ R.isTrivial :=
  ⟨(isTrivial_of_len_pts_sub_one_eq_zero ·), (len_pts_sub_one_eq_zero_of_isTrivial ·)⟩

theorem len_rgs_eq_zero_of_isTrivial (h : R.isTrivial) : R.regions.length = 0 := sorry
theorem isTrivial_of_len_rgs_eq_zero (h : R.regions.length = 0) : R.isTrivial := sorry
@[simp] theorem len_rgs_eq_zero_iff_isTrivial : R.regions.length = 0 ↔ R.isTrivial :=
  ⟨(isTrivial_of_len_rgs_eq_zero ·), (len_rgs_eq_zero_of_isTrivial ·)⟩

theorem rgs_eq_nil_of_isTrivial (h : R.isTrivial) : R.regions = [] := sorry
theorem isTrivial_of_rgs_eq_nil (h : R.regions = []) : R.isTrivial := sorry
@[simp] theorem rgs_eq_nil_iff_isTrivial : R.regions = [] ↔ R.isTrivial :=
  ⟨(R.isTrivial_of_rgs_eq_nil ·), (R.rgs_eq_nil_of_isTrivial ·)⟩

@[simp] theorem len_rgs_ne_zero_iff_not_isTrivial : R.regions.length ≠ 0 ↔ ¬R.isTrivial := sorry
@[simp] theorem len_rgs_pos_iff_not_isTrivial : 0 < R.regions.length ↔ ¬R.isTrivial := sorry
@[simp] theorem rgs_ne_nil_iff_not_isTrivial : R.regions ≠ [] ↔ ¬R.isTrivial := sorry




end Rollercoaster
