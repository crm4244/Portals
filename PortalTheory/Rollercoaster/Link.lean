import PortalTheory.Rollercoaster.Basic


namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



variable {U : 𝒰} (ha : a ∈ U.1) (hb : b ∈ U.1)


def link : Rollercoaster 𝒰 a b where
  points := [a, b]
  regions := [U]
  len_rgs_add_one_eq_len_pts := by simp
  mem_rgs := by simp [ha]
  succ_mem_rgs := by simp [hb]
  head_pts_eq := rfl
  getLast_pts_eq := rfl


@[simp] theorem rgs_link : (link ha hb).regions = [U] := rfl
@[simp] theorem len_rgs_link : (link ha hb).regions.length = 1 := by simp
@[simp] theorem pts_link : (link ha hb).points = [a, b] := rfl
@[simp] theorem len_pts_link : (link ha hb).points.length = 2 := by simp
@[simp] theorem getElem_one_pts_link : (link ha hb).points[1] = b := sorry

theorem eq_link_iff_rgs_eq_singleton : R = link ha hb ↔ R.regions = [U] := sorry
theorem eq_link_iff_len_rgs_eq : R = link ha hb ↔ R.regions.length = 1 := sorry
theorem eq_link_iff_len_pts_eq : R = link ha hb ↔ R.points.length = 2 := sorry



end Rollercoaster
