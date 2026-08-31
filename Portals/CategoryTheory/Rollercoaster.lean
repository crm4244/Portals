import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected

open Topology TopologicalSpace

variable {α : Type*}



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


@[simp] theorem getElem_zero : R.points[0]'R.len_pts_pos = a := by

  sorry
@[simp] theorem getElem_len_pts_sub_one : R.points[R.points.length - 1]'sorry = b := sorry
@[simp] theorem getElem_len_rgs : R.points[R.regions.length]'sorry = b := sorry






section trivial

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


end trivial





section of_pair

variable {U : 𝒰} (ha : a ∈ U.1) (hb : b ∈ U.1)


def of_pair : Rollercoaster 𝒰 a b where
  points := [a, b]
  regions := [U]
  len_rgs_add_one_eq_len_pts := by simp
  mem_rgs := by simp [ha]
  succ_mem_rgs := by simp [hb]
  head_pts_eq := rfl
  getLast_pts_eq := rfl


@[simp] theorem rgs_ofPair : (of_pair ha hb).regions = [U] := rfl
@[simp] theorem len_rgs_ofPair : (of_pair ha hb).regions.length = 1 := by simp
@[simp] theorem pts_ofPair : (of_pair ha hb).points = [a, b] := rfl
@[simp] theorem len_pts_ofPair : (of_pair ha hb).points.length = 2 := by simp
@[simp] theorem getElem_one_pts_ofPair : (of_pair ha hb).points[1] = b := sorry

theorem eq_ofPair_iff_rgs_eq_singleton : R = of_pair ha hb ↔ R.regions = [U] := sorry
theorem eq_ofPair_iff_len_rgs_eq_one : R = of_pair ha hb ↔ R.regions.length = 1 := sorry
theorem eq_ofPair_iff_len_pts_eq_two : R = of_pair ha hb ↔ R.points.length = 2 := sorry

theorem not_isTrivial_ofPair {ha : a ∈ U.1} {hb : b ∈ U.1} : ¬(of_pair ha hb).isTrivial := sorry


end of_pair





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
theorem isTrivial_drop_len_pts_sub_one :
  R.drop (n := R.points.length - 1) (Nat.sub_one_lt R.len_pts_ne_zero) |>.isTrivial := sorry




end drop





-- need both of these for induction
#check List.drop
#check List.take


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





def heq_rec {motive : {a b : α} → Rollercoaster 𝒰 a b → Sort*}
  {a b a' b' : α} (ha : a = a') (hb : b = b')
  {R : Rollercoaster 𝒰 a b} {R' : Rollercoaster 𝒰 a' b'} (h : R ≍ R') : motive R → motive R' :=
    fun hR ↦ by cases ha; cases hb; cases h; exact hR


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



section jumps

variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)


lemma f_heq
  {U U' : 𝒰} (hU : U = U')
  {p : U.1} {p' : U'.1} (hp : p ≍ p')
  {q : U.1} {q' : U'.1} (hq : q ≍ q')
  {x : T p.1} {x' : T p'.1} (hx : x ≍ x') :
    @f U p q x ≍ @f U' p' q' x' :=
  by cases hU; cases hp; cases hq; cases hx; rfl


def fin_regions_of_points_pred (n : Fin (R.points.length - 1)) :
  Fin R.regions.length := ⟨n, R.length_regions_eq.symm ▸ n.2⟩


def jump (n : Fin (R.points.length - 1)) := @f (R.regions[fin_regions_of_points_pred n])
  ⟨R.points[n], R.mem_region (fin_regions_of_points_pred n)⟩
  ⟨R.points[n.succ]' (Nat.add_lt_of_lt_sub n.2), R.next_mem_region (fin_regions_of_points_pred n)⟩


theorem jump_cast_apply {a' b' : α} {R' : Rollercoaster 𝒰 a' b'}
  {n : Fin (R.points.length - 1)} {n' : Fin (R'.points.length - 1)}
  (h_n : R.points[n] = R'.points[n'])
  (h_succ : R.points[↑n + 1] = R'.points[↑n' + 1])
  (h_region : R.regions[fin_regions_of_points_pred n] =
    R'.regions[fin_regions_of_points_pred n'])
  (x : T R.points[n]) :
    R'.jump f n' (cast (congr_arg T h_n) x) =
    cast (congr_arg T h_succ) (R.jump f n x) :=
  eq_cast_iff_heq.mpr <| f_heq f h_region.symm
    (Subtype.heq_iff_coe_eq (fun _ ↦ h_region ▸ Iff.rfl) |>.mpr h_n.symm)
    (Subtype.heq_iff_coe_eq (fun _ ↦ h_region ▸ Iff.rfl) |>.mpr h_succ.symm)
    (cast_heq_iff_heq _ _ _ |>.mpr HEq.rfl)


def jumpTo : (n : Fin R.points.length) → T (R.points[0]'R.length_points_pos) → T R.points[n]
  | ⟨0, _⟩ => id
  | ⟨n + 1, h⟩ => jump f ⟨n, Nat.lt_pred_of_succ_lt h⟩ ∘ jumpTo ⟨n, Nat.lt_succ_self n |>.trans h⟩


theorem jumpTo_eq_of_eq {n n' : Fin R.points.length} (h : n = n') :
  jumpTo f n = cast (congr_arg (T R.points[·]) h.symm) ∘ (R.jumpTo f n') := by cases h; rfl


theorem jumpTo_eq_of_eq_zero {n : Fin R.points.length} (h : n.1 = 0) :
  jumpTo f n = cast (congr_arg (T R.points[·]) <|
    Fin.mk_eq_mk (h := R.length_points_pos) |>.mpr h.symm) :=
  jumpTo_eq_of_eq f (Fin.eq_mk_iff_val_eq (hk := h ▸ n.2) |>.mpr h) |>.trans <|
    congr_arg _ <| jumpTo.eq_def _ _


theorem jumpTo_eq_of_eq_succ {n : Fin R.points.length} {n' : ℕ} (h : n = n'.succ) :
  R.jumpTo f n =
    cast (congr_arg (T ∘ R.points.get) <| Fin.eq_mk_iff_val_eq (hk := h ▸ n.2) |>.mpr h |>.symm)
    ∘ (R.jump f ⟨n', Nat.lt_pred_of_succ_lt <| h ▸ n.2⟩)
    ∘ (R.jumpTo f ⟨n', Nat.lt_of_succ_lt <| h ▸ n.2⟩) :=
  jumpTo_eq_of_eq f (Fin.eq_mk_iff_val_eq (hk := h ▸ n.2) |>.mpr h) |>.trans <|
    congr_arg _ <| jumpTo.eq_def _ _


theorem jumpTo_cast_apply {a' b' : α} {R' : Rollercoaster 𝒰 a' b'} {n : ℕ}
  (hnR : n < R.points.length) (hnR' : n < R'.points.length)
  (h_points_eq : ∀ (i : ℕ) (hi : i ≤ n),
    R.points[i]'(lt_of_le_of_lt hi hnR) = R'.points[i]'(lt_of_le_of_lt hi hnR'))
  (h_regions_eq : ∀ (i : ℕ) (hi : i < n),
    R.regions[i]'(lt_of_lt_of_le hi <| Nat.le_of_lt_add_one <| R.h_length ▸ hnR) =
    R'.regions[i]'(lt_of_lt_of_le hi <| Nat.le_of_lt_add_one <| R'.h_length ▸ hnR'))
  (x : T R.points[0]) :
    R'.jumpTo f ⟨n, hnR'⟩ (cast (congr_arg T <| h_points_eq 0 <| Nat.zero_le n) x) =
      cast (congr_arg T <| h_points_eq n le_rfl) (R.jumpTo f ⟨n, hnR⟩ x) := by

  induction n with
  | zero => unfold jumpTo; rfl
  | succ n h_ind =>
    simp only [jumpTo, Function.comp_apply]
    rw [h_ind (Nat.lt_of_succ_lt hnR) (Nat.lt_of_succ_lt hnR')
      (fun i hi ↦ h_points_eq i <| Nat.le_succ_of_le hi)
      (fun i hi ↦ h_regions_eq i <| Nat.lt_succ_of_lt hi) x]
    exact R.jump_cast_apply f
      (n := ⟨n, Nat.lt_pred_of_succ_lt hnR⟩) (n' := ⟨n, Nat.lt_pred_of_succ_lt hnR'⟩)
      (h_points_eq n <| Nat.le_succ n) (h_points_eq n.succ le_rfl)
      (h_regions_eq n <| Nat.lt_succ_self n) _


def jumpAll : T a → T b := fun x ↦
  cast (congr_arg T <| List.getLast_eq_getElem R.points_ne_nil |>.symm.trans R.last_eq) <|
    R.jumpTo f ⟨R.points.length - 1, Nat.sub_one_lt R.length_points_ne_zero⟩ <|
    cast (congr_arg T <| R.head_eq.symm.trans <| List.head_eq_getElem R.points_ne_nil) x


end jumps





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


theorem length_regions_map : (R.map h).regions.length = R.regions.length := sorry


theorem getElem_map (n : Fin (R.map h).points.length) :
  (R.map h).points[n] = m (R.points[n]' (R.length_map h ▸ n.2)) :=
    List.getElem_map _



variable {T : β → Type*}
variable (f : {U : 𝒰'} → (p : U.1) → (q : U.1) → T p.1 → T q.1)


open Classical in theorem jump_map_apply (n : Fin (R.points.length - 1))
  (x : T <| m <| R.points[0]' length_points_pos) :

  let n' : Fin ((map h).points.length - 1) := ⟨n, lt_of_eq_of_lt' (length_regions_map h).symm n.2⟩
  let hn : T (m R.points[n'.castSucc.cast _]) = T (R.map h).points[n'] :=
    congr_arg T <| R.getElem_map h (n'.castSucc.cast <| Nat.sub_one_add_one length_points_ne_zero)
      |>.symm.trans <| Fin.getElem_fin _ _ _
  (R.map h).jump f n' x = R.jump (fun {U} ⟨p, hp⟩ ⟨q, hq⟩ ↦ let hU := choose_spec (h U)
      @f ⟨choose (h U), hU.1⟩ ⟨m p, hU.2 ⟨p, hp, rfl⟩⟩ ⟨m q, hU.2 ⟨q, hq, rfl⟩⟩) n x := sorry


open Classical in theorem jumpTo_map_apply (n : Fin R.points.length) (x : T <| m <| R.points[0]'R.length_points_pos) :
  let n' : Fin (R.map h).points.length := ⟨n, lt_of_eq_of_lt' (R.length_map h).symm n.2⟩
  let hn : T (m R.points[n']) = T (R.map h).points[n'] :=
    congr_arg T <| (R.getElem_map h n').symm.trans <| Fin.getElem_fin _ _ _
  (R.map h).jumpTo (T := T) f n' x = hn ▸ R.jumpTo (T := T ∘ m)
    (fun {U} ⟨p, hp⟩ ⟨q, hq⟩ ↦ let hU := choose_spec (h U)
      @f ⟨choose (h U), hU.1⟩ ⟨m p, hU.2 ⟨p, hp, rfl⟩⟩ ⟨m q, hU.2 ⟨q, hq, rfl⟩⟩) n x := sorry


open Classical in theorem jumpAll_map_apply (x : T (m a)) :
  (R.map h).jumpAll (T := T) f x = R.jumpAll (T := T ∘ m)
    (fun {U} ⟨p, hp⟩ ⟨q, hq⟩ ↦ let hU := choose_spec (h U)
      @f ⟨choose (h U), hU.1⟩ ⟨m p, hU.2 ⟨p, hp, rfl⟩⟩ ⟨m q, hU.2 ⟨q, hq, rfl⟩⟩) x := by

  induction hn : R.regions.length with
  | zero =>
    unfold jumpAll
    rw [jumpTo_eq_of_eq_zero f (by simp only [R.length_map h, R.length_regions_eq.symm, hn]),
      jumpTo_eq_of_eq_zero _ (by simp only [R.length_regions_eq.symm, hn])]
    simp only [cast_cast]
  | succ n h_ind =>


    sorry

end map





section append
variable {c : α} (R) (R' : Rollercoaster 𝒰 b c)

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


instance : HAppend (Rollercoaster 𝒰 a b) (Rollercoaster 𝒰 b c) (Rollercoaster 𝒰 a c) :=
  ⟨(append · ·)⟩


theorem length_append :
  (R ++ R').points.length = R.points.length + R'.points.length - 1 :=
    List.length_append.trans <| List.length_tail ▸ Nat.add_sub_assoc
      (Nat.one_le_of_lt R'.length_points_pos) _ |>.symm



variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)


theorem jumpAll_append_apply {c : α} (R' : Rollercoaster 𝒰 b c) (x : T a) :
  (R ++ R').jumpAll f x = R'.jumpAll f (R.jumpAll f x) := by
  induction hn : R'.regions.length with
  | zero =>

    have h1 : R'.points.length - 1 = 0 := sorry
    have h2 : (Fin.mk (R'.points.length - 1) (Nat.pred_lt_self R'.length_points_pos)).val = 0 := h1

    have h3 : (R ++ R').points.length - 1 = R.points.length - 1 :=
      congr_arg (· - 1) <| length_append _ _ |>.trans <|
        Nat.add_sub_assoc (Nat.one_le_of_lt R'.length_points_pos) _ |>.trans <|
          h1 ▸ Nat.add_zero _
    have h4 : R.points.length - 1 < R.points.length := Nat.pred_lt_self R.length_points_pos
    have h5 : R.points.length - 1 < (R ++ R').points.length := sorry

    have h := jumpTo_cast_apply f h4 h5
      (fun i hi ↦ (List.getElem_append
        (lt_of_le_of_lt hi h5) |>.trans <|
        dif_pos (lt_of_le_of_lt hi <| Nat.pred_lt_self R.length_points_pos) |>.trans rfl).symm)
      (fun i hi ↦ (List.getElem_append
        (List.length_append ▸ hn ▸ R.length_regions_eq.symm ▸ hi) |>.trans <|
        dif_pos (R.length_regions_eq.symm ▸ hi)).symm)
      (cast jumpAll._proof_4 x)
    rw [cast_cast] at h

    simp only [jumpAll, jumpTo_eq_of_eq f (Fin.mk_eq_mk (h' := h5) |>.mpr h3),
      Function.comp_apply, h, jumpTo_eq_of_eq_zero f h2, cast_cast]

  | succ n ih =>

    unfold jumpAll
    #check jumpTo_eq_of_eq_succ f

    sorry


theorem jumpAll_append {c : α} {R' : Rollercoaster 𝒰 b c} :
  (R ++ R').jumpAll f = R'.jumpAll f ∘ R.jumpAll f :=
    funext (jumpAll_append_apply _ _ _ ·)


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
        ⟨of_pair hx <| endPoint_mem_region_of_minimal U h_minimal⟩)
      (fun h_minimal : ¬@Minimal 𝒰 preorder.toLE Set.univ U ↦
        let ⟨y, hyU, V, hyV, hVU⟩ := exists_lt_of_not_minimal U h_minimal
        ⟨(of_pair hx hyU).append <| Classical.choice <| h_ind V hVU y hyV⟩))


noncomputable def bot_to_top [TopologicalSpace α] [CompleteLinearOrder α]
  [DenselyOrdered α] [OrderTopology α] [CompactSpace α]
  (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ x : α, ∃ U ∈ 𝒰, x ∈ U) :
    Rollercoaster 𝒰 ⊥ ⊤ := by

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

  choose t t_cover using ‹CompactSpace α›.isCompact_univ.elim_finite_subcover
    (@Subtype.val _ {U | U ∈ 𝒰 ∧ Nonempty U}) (fun ⟨U, hU, _⟩ ↦ h_open ⟨U, hU⟩)
      (fun x _ ↦ let ⟨U, hU, hx⟩ := h_cover x; ⟨U, ⟨⟨U, hU, ⟨x, hx⟩⟩, rfl⟩, hx⟩)
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
      have h_lt_of_mem : ∀ x ∈ U.1, x < sSup U :=
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
        ⟨_, h_lt_of_mem _ (Classical.choice U.2.2).2⟩
      let ⟨x, hx, hxl⟩ := lt_sSup_iff.mp hl
      ⟨x, hx, ⟨V, ⟨V, hV, hV_nonempty⟩, hVt, rfl⟩,
        hlioc <| Set.mem_Ioc.mpr ⟨hxl, le_sSup hx⟩, sSup U, hsup, h_lt_of_mem⟩

  choose _ x0 x1 using t_cover <| Set.mem_univ ⊥
  choose U x00 using x0
  cases x00
  choose _ x10 h_bot using x1
  choose hU x11 using x10
  cases x11

  obtain R' := Classical.choice <|
    @nonempty_of_finite_preorder_from α t_set _ (supOrder.lift Subtype.val)
      ⊤ (top_mem_iff_minimal_t · |>.mp) exists_lt_of_not_minimal_t ⟨U, U, hU, rfl⟩ ⊥ h_bot
  exact R'.map (m := id) (fun ⟨_, ⟨⟨U, hU, _⟩, _, rfl⟩⟩ ↦ ⟨U, hU, fun _ ⟨_, h, rfl⟩ ↦ h⟩)




open unitInterval

variable [TopologicalSpace α]



def follows (f : C(I, α)) : Prop := ∃ i : Fin R.points.length → I,
  f ∘ i = R.points.get ∧
  StrictMono i ∧
  i ⟨0, R.len_pts_pos⟩ = 0 ∧
  i ⟨R.points.length - 1, Nat.pred_lt R.len_pts_ne_zero⟩ = 1 ∧
  ∀ (x : I) (n : Fin R.regions.length),
    i ⟨n, n.2.trans R.len_rgs_lt_len_pts⟩ ≤ x ∧
    x ≤ i ⟨n.succ, R.len_rgs_add_one_eq_len_pts ▸ Nat.succ_lt_succ n.2⟩ →
      f x ∈ R.regions[n].1




theorem nonempty_of_path (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ x : α, ∃ U ∈ 𝒰, x ∈ U)
  (path : C(I, α)) : Nonempty (Rollercoaster 𝒰 (path 0) (path 1)) :=
  ⟨@map I {path ⁻¹' U | U : 𝒰} 0 1
    (bot_to_top (fun ⟨_, _, rfl⟩ ↦ path.continuous.isOpen_preimage _ <| h_open _)
      (fun x ↦ let ⟨U, hU, hx⟩ := h_cover <| path x; ⟨path ⁻¹' U, ⟨⟨U, hU⟩, rfl⟩, hx⟩))
    _ _ _ fun ⟨_, ⟨U, h⟩, rfl⟩ ↦ ⟨U, h, Set.image_subset_iff.mpr subset_rfl⟩⟩



theorem exists_path_follows (h_pathconnected : ∀ U ∈ 𝒰, IsPathConnected U) :
    ∃ x : Path a b, R.follows x := by


  sorry







variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)



def rel (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1) :
  Rollercoaster 𝒰 a b → Rollercoaster 𝒰 a b → Prop :=
    fun R1 R2 ↦ R1.jumpAll f = R2.jumpAll f



variable (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ a : α, ∃ U : 𝒰, a ∈ U.1)

variable {f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1}
variable (f_id : ∀ {U : 𝒰} (p : U.1), f p p = id)
variable (f_trans : ∀ {U : 𝒰} (p q r : U.1), f q r ∘ f p q = f p r)
variable (f_inter : ∀ {U V : 𝒰} {p q : α} (hpU : p ∈ U.1) (hpV : p ∈ V.1)
  (hqU : q ∈ U.1) (hqV : q ∈ V.1), f ⟨p, hpU⟩ ⟨q, hqU⟩ = f ⟨p, hpV⟩ ⟨q, hqV⟩)





theorem rel_of_homotopy {φ : I → I → α} (h_continuous : Continuous φ)
  {R : Rollercoaster 𝒰 a b} (h_follows : R.follows (φ 0))
  {R' : Rollercoaster 𝒰 a b} (h_follows' : R'.follows (φ 1))
  (h_endpoints : ∀ x, φ x 0 = a ∧ φ x 1 = b) :
    rel f R R' := sorry




end Rollercoaster
