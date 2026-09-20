import PortalTheory.Rollercoaster.Trivial
import PortalTheory.Rollercoaster.Operations
import PortalTheory.Rollercoaster.Lemmas


namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



theorem induction_drop {P : {a b : α} → Rollercoaster 𝒰 a b → Prop}
  (h_trivial : P (trivial 𝒰 b))
  (h_ind : ∀ (n : ℕ) (hn : n < R.points.length - 1),
    P (R.drop (n := n + 1) <| Nat.add_lt_of_lt_sub hn) →
    P (R.drop (n := n) <| hn.trans <| Nat.pred_lt_self R.len_pts_pos)) : P R :=
  heq_rec R.getElem_zero rfl R.drop_zero <| Nat.decreasingInduction
    (n := R.points.length - 1)
    (motive := fun n hn ↦ P <| R.drop (n := n) <| Nat.lt_of_le_pred R.len_pts_pos hn) h_ind
    (heq_rec R.getElem_len_pts_sub_one.symm rfl (isTrivial_drop_len_pts_sub_one (R := R) |>.trans <|
      trivial_heq_of_eq (𝒰 := 𝒰) R.getElem_len_pts_sub_one).symm h_trivial)
    (Nat.zero_le _)



theorem induction_take {P : {a b : α} → Rollercoaster 𝒰 a b → Prop}
  (h_trivial : P (trivial 𝒰 a))
  (h_ind : ∀ (n : ℕ) (hn : n < R.points.length - 2),
    P (R.take (n := n) <| hn.trans sorry) →
    P (R.take (n := n + 1) sorry)) : P R := sorry



end Rollercoaster
