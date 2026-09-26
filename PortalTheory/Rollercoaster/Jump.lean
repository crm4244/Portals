import PortalTheory.Rollercoaster.Basic
import PortalTheory.Rollercoaster.Operations



namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}

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
  Fin R.regions.length := ⟨n, R.len_rgs_eq_len_pts_sub_one.symm ▸ n.2⟩


def jump (n : Fin (R.points.length - 1)) := @f (R.regions[fin_regions_of_points_pred n])
  ⟨R.points[n], R.mem_rgs (fin_regions_of_points_pred n)⟩
  ⟨R.points[n.succ]' (Nat.add_lt_of_lt_sub n.2), R.succ_mem_rgs (fin_regions_of_points_pred n)⟩


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


def jumpTo : (n : Fin R.points.length) → T (R.points[0]'R.len_pts_pos) → T R.points[n]
  | ⟨0, _⟩ => id
  | ⟨n + 1, h⟩ => jump f ⟨n, Nat.lt_pred_of_succ_lt h⟩ ∘ jumpTo ⟨n, Nat.lt_succ_self n |>.trans h⟩


theorem jumpTo_eq_of_eq {n n' : Fin R.points.length} (h : n = n') :
  jumpTo f n = cast (congr_arg (T R.points[·]) h.symm) ∘ (R.jumpTo f n') := by cases h; rfl


theorem jumpTo_eq_of_eq_zero {n : Fin R.points.length} (h : n.1 = 0) :
  jumpTo f n = cast (congr_arg (T R.points[·]) <|
    Fin.mk_eq_mk (h := R.len_pts_pos) |>.mpr h.symm) :=
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
    R.regions[i]'(lt_of_lt_of_le hi <| Nat.le_of_lt_add_one <| R.len_rgs_add_one_eq_len_pts ▸ hnR) =
    R'.regions[i]'(lt_of_lt_of_le hi <| Nat.le_of_lt_add_one <|
      R'.len_rgs_add_one_eq_len_pts ▸ hnR'))
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
  cast (congr_arg T <| List.getLast_eq_getElem R.pts_ne_nil |>.symm.trans R.getLast_pts_eq) <|
    R.jumpTo f ⟨R.points.length - 1, Nat.sub_one_lt R.len_pts_ne_zero⟩ <|
    cast (congr_arg T <| R.head_pts_eq.symm.trans <| List.head_eq_getElem R.pts_ne_nil) x


theorem jumpAll_induction {P : {x : α} → T x → Prop} {x : T a} (h0 : P x)
  (h_ind : ∀ {U : 𝒰} {p q : U.1} (y : T p.1), P y → P (f p q y)) :
    P (R.jumpAll f x) := by
  sorry




/-
section map

variable {β : Type*} {m : α → β} {𝒰' : Set (Set β)}
variable (h : ∀ A : 𝒰, ∃ A' ∈ 𝒰', m '' A ⊆ A')



open Classical in theorem jump_map_apply (n : Fin (R.points.length - 1))
  (x : T <| m <| R.points[0]' len_pts_pos) :

  let n' : Fin ((map h).points.length - 1) := ⟨n, lt_of_eq_of_lt' (len_rgs_map h).symm n.2⟩
  let hn : T (m R.points[n'.castSucc.cast _]) = T (R.map h).points[n'] :=
    congr_arg T <| R.getElem_map h (n'.castSucc.cast <| Nat.sub_one_add_one len_pts_ne_zero)
      |>.symm.trans <| Fin.getElem_fin _ _ _
  (R.map h).jump f n' x = R.jump (fun {U} ⟨p, hp⟩ ⟨q, hq⟩ ↦ let hU := choose_spec (h U)
      @f ⟨choose (h U), hU.1⟩ ⟨m p, hU.2 ⟨p, hp, rfl⟩⟩ ⟨m q, hU.2 ⟨q, hq, rfl⟩⟩) n x := sorry


open Classical in theorem jumpTo_map_apply (n : Fin R.points.length) (x : T <| m <| R.points[0]'R.len_pts_pos) :
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
-/



section append

variable {c : α} (R) (R' : Rollercoaster 𝒰 b c)



theorem jumpAll_append_apply (x : T a) :
  (R ++ R').jumpAll f x = R'.jumpAll f (R.jumpAll f x) := by
  induction hn : R'.regions.length with
  | zero =>

    have h1 : R'.points.length - 1 = 0 := sorry
    have h2 : (Fin.mk (R'.points.length - 1) (Nat.pred_lt_self R'.len_pts_pos)).val = 0 := h1

    have h3 : (R ++ R').points.length - 1 = R.points.length - 1 :=
      congr_arg (· - 1) <| length_pts_append _ _ |>.trans <|
        Nat.add_sub_assoc (Nat.one_le_of_lt R'.len_pts_pos) _ |>.trans <|
          h1 ▸ Nat.add_zero _
    have h4 : R.points.length - 1 < R.points.length := Nat.pred_lt_self R.len_pts_pos
    have h5 : R.points.length - 1 < (R ++ R').points.length := sorry

    have h := jumpTo_cast_apply f h4 h5
      (fun i hi ↦ (List.getElem_append
        (lt_of_le_of_lt hi h5) |>.trans <|
        dif_pos (lt_of_le_of_lt hi <| Nat.pred_lt_self R.len_pts_pos) |>.trans rfl).symm)
      (fun i hi ↦ (List.getElem_append
        (List.length_append ▸ hn ▸ R.len_rgs_eq_len_pts_sub_one.symm ▸ hi) |>.trans <|
        dif_pos (R.len_rgs_eq_len_pts_sub_one.symm ▸ hi)).symm)
      (cast jumpAll._proof_4 x)
    rw [cast_cast] at h

    simp only [jumpAll, jumpTo_eq_of_eq f (Fin.mk_eq_mk (h' := h5) |>.mpr h3),
      Function.comp_apply, h, jumpTo_eq_of_eq_zero f h2, cast_cast]

  | succ n ih =>

    unfold jumpAll
    #check jumpTo_eq_of_eq_succ f

    sorry


theorem jumpAll_append : (R ++ R').jumpAll f = R'.jumpAll f ∘ R.jumpAll f :=
  funext (jumpAll_append_apply _ _ _ ·)



end append



end Rollercoaster
