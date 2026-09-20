import PortalTheory.Rollercoaster.Link
import PortalTheory.Rollercoaster.Operations


namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



theorem not_isTrivial_link {U : 𝒰} {ha : a ∈ U.1} {hb : b ∈ U.1} : ¬(link ha hb).isTrivial := sorry

theorem isTrivial_drop_len_pts_sub_one :
  R.drop (n := R.points.length - 1) (Nat.sub_one_lt R.len_pts_ne_zero) |>.isTrivial := sorry



end Rollercoaster
