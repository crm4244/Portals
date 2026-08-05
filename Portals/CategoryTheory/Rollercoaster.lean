--import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens

open Topology TopologicalSpace

variable {α : Type*} [TopologicalSpace α]



structure Rollercoaster (𝒪 : Set (Opens α)) where
  list_of_points : List α
  list_of_opens : List 𝒪
  h_length : list_of_opens.length + 1 = list_of_points.length
  t_mem : ∀ n : Fin list_of_opens.length, list_of_points[n] ∈ list_of_opens[n].1
  t_next_mem : ∀ n : Fin list_of_opens.length, list_of_points[n.succ] ∈ list_of_opens[n].1



namespace Rollercoaster

variable {𝒪 : Set (Opens α)}
variable {R : Rollercoaster 𝒪}

theorem len_opens_lt_len_points : R.list_of_opens.length < R.list_of_points.length :=
  R.h_length ▸ Nat.lt_add_one _

theorem len_points_pos : 0 < R.list_of_points.length :=
  R.h_length ▸ Nat.zero_lt_succ _

theorem len_points_neq_zero : R.list_of_points.length ≠ 0 :=
  R.h_length ▸ by aesop

theorem points_neq_nil : R.list_of_points ≠ [] :=
  List.ne_nil_of_length_pos R.len_points_pos



def head : α := R.list_of_points.head R.points_neq_nil
def last : α := R.list_of_points.getLast R.points_neq_nil


/-
theorem head_eq_last (h : R.list_of_opens.length = 0) : R.head = R.last :=
  List.head_eq_getElem R.points_neq_nil |>.trans
    (List.getLast_eq_getElem R.points_neq_nil |>.trans
      (by congr; exact R.h_length ▸ h) |>.symm)
-/



variable {β γ : Type*} {T : α → Type*}

section jump_defs
variable (f : {U : 𝒪} → (p : U.1) → (q : U.1) → T p.1 → T q.1)


def jump (n : Fin R.list_of_opens.length) := @f R.list_of_opens[n]
  ⟨R.list_of_points.get (n.castSucc.cast R.h_length), R.t_mem n⟩
  ⟨R.list_of_points.get (n.succ.cast R.h_length), R.t_next_mem n⟩


def jump_head_to : (n : ℕ) → (_ : n < R.list_of_points.length) → T R.head → T R.list_of_points[n]
  | 0 => fun _ ↦ List.head_eq_getElem R.points_neq_nil ▸ id
  | n + 1 => fun h ↦ R.jump f ⟨n, Nat.add_one_lt_add_one_iff.mp (R.h_length.symm ▸ h)⟩ ∘
    jump_head_to n (Nat.lt_succ_self n |>.trans h)


def jump_all : T R.head → T R.last := fun a ↦ by
  unfold last
  rw [List.getLast_eq_getElem R.points_neq_nil]
  exact R.jump_head_to (T := T) f (R.list_of_points.length - 1)
    (Nat.sub_one_lt R.len_points_neq_zero) a

end jump_defs


variable [PredOrder 𝒪] [WellFoundedLT 𝒪]
variable (𝒪_cover : ∀ a : α, ∃ U : 𝒪, a ∈ U.1)
variable (𝒪_ordered_overlap : ∀ U : 𝒪, ¬Minimal 𝒪 U →
  ∃ a : α, a ∈ U.1 ∧ ∃ V : 𝒪, a ∈ V.1 ∧ V < U)

variable {f : {U : 𝒪} → (p : U.1) → (q : U.1) → T p.1 → T q.1}
variable (f_comp : ∀ {U : 𝒪} (p q r : U.1), f q r ∘ f p q = f p r)
variable (f_overlap : ∀ {U V : 𝒪} {p q : α} (hpU : p ∈ U.1) (hpV : p ∈ V.1)
  (hqU : q ∈ U.1) (hqV : q ∈ V.1), f ⟨p, hpU⟩ ⟨q, hqU⟩ = f ⟨p, hpV⟩ ⟨q, hqV⟩)



theorem jump_all_eq_jump_all_apply {R' : Rollercoaster 𝒪}
  (h_head_eq : R.head = R'.head) (h_last_eq : R.last = R'.last) (a : T R.head) :
    R.jump_all f a = h_last_eq ▸ R'.jump_all f (h_head_eq ▸ a) := by

  #check WellFounded.induction
  sorry


end Rollercoaster
