import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.Homotopy.Path

open Topology TopologicalSpace

variable {α : Type*}



-- rename Rollercoaster to Chainway

structure Rollercoaster (𝒰 : Set (Set α)) (a b : α) where
  points : List α
  regions : List 𝒰

  len_rgs_add_one_eq_len_pts : regions.length + 1 = points.length
  pts_ne_nil : points ≠ [] := List.ne_nil_of_length_eq_add_one len_rgs_add_one_eq_len_pts.symm

  mem_rgs : ∀ n : Fin regions.length, points[n] ∈ regions[n].1
  succ_mem_rgs : ∀ n : Fin regions.length, points[n.succ] ∈ regions[n].1

  head_pts_eq : points.head pts_ne_nil = a
  getLast_pts_eq : points.getLast pts_ne_nil = b



namespace Rollercoaster

variable {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



def head : α := a
def last : α := b


theorem len_rgs_eq_len_pts_sub_one : R.regions.length = R.points.length - 1 :=
  Nat.eq_sub_of_add_eq R.len_rgs_add_one_eq_len_pts

theorem len_rgs_lt_len_pts : R.regions.length < R.points.length :=
  R.len_rgs_add_one_eq_len_pts ▸ Nat.lt_succ_self _

theorem len_pts_ne_zero : R.points.length ≠ 0 :=
  Nat.ne_zero_of_lt R.len_rgs_lt_len_pts

theorem len_pts_pos : 0 < R.points.length :=
  Nat.pos_of_ne_zero R.len_pts_ne_zero

theorem not_isEmpty_pts : ¬R.points.isEmpty :=
  (R.pts_ne_nil <| List.isEmpty_iff.mp ·)

theorem head_mem_pts : a ∈ R.points :=
  List.mem_of_head? <| List.head?_eq_head R.pts_ne_nil |>.trans <|
    congr_arg some R.head_pts_eq

theorem last_mem_pts : b ∈ R.points :=
  List.mem_of_getLast? <| List.getLast?_eq_getLast R.pts_ne_nil |>.trans <|
    congr_arg some R.getLast_pts_eq


@[simp] theorem getElem_zero : R.points[0]'R.len_pts_pos = a := by sorry
@[simp] theorem getElem_len_pts_sub_one : R.points[R.points.length - 1]'sorry = b := sorry
@[simp] theorem getElem_len_rgs : R.points[R.regions.length]'sorry = b := sorry



def heq_rec {motive : {a b : α} → Rollercoaster 𝒰 a b → Sort*}
  {a b a' b' : α} (ha : a = a') (hb : b = b')
  {R : Rollercoaster 𝒰 a b} {R' : Rollercoaster 𝒰 a' b'} (h : R ≍ R') : motive R → motive R' :=
    fun hR ↦ by cases ha; cases hb; cases h; exact hR





end Rollercoaster
