import PortalTheory.Rollercoaster.Link
import PortalTheory.Rollercoaster.Operations
import PortalTheory.Rollercoaster.Induction
import PortalTheory.Rollercoaster.Jump
import Mathlib.Topology.Algebra.Module.LocallyConvex





open unitInterval

instance : LocPathConnectedSpace I := Convex.locPathConnectedSpace ℝ (convex_Icc 0 1)





namespace Rollercoaster

variable {α : Type*} {𝒰 : Set (Set α)} {a b : α}
variable {R : Rollercoaster 𝒰 a b}



theorem exists_strictMono [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
  [Finite 𝒰] {preorder : Preorder 𝒰} {endpoint : α}
  (endPoint_mem_region_of_minimal : ∀ U : 𝒰, @Minimal 𝒰 preorder.toLE Set.univ U → endpoint ∈ U.1)
  (exists_lt_of_not_minimal : ∀ U : 𝒰, ¬@Minimal 𝒰 preorder.toLE Set.univ U →
    ∀ x ∈ U.1, ∃ y ∈ U.1, x < y ∧ y < endpoint ∧ ∃ V : 𝒰, y ∈ V.1 ∧ preorder.lt V U) {U' : 𝒰} :
      ∀ x ∈ U'.1, x < endpoint → ∃ R : Rollercoaster 𝒰 x endpoint, StrictMono R.points.get :=
  @Finite.to_wellFoundedLT.induction 𝒰 preorder.toLT
    (fun U ↦ ∀ x ∈ U.1, x < endpoint → ∃ R : Rollercoaster 𝒰 x endpoint, StrictMono R.points.get) U'
    (fun U h_ind x hx ↦ by_cases
      (fun (h_minimal : @Minimal 𝒰 preorder.toLE Set.univ U) h_lt_endpoint ↦
        ⟨link hx <| endPoint_mem_region_of_minimal U h_minimal, fun a b hab ↦
          match ha : a.1 with
          | 0 => by
            simp [ha, eq_of_le_of_ge (Nat.le_of_lt_succ b.isLt)
              (Nat.succ_le_of_lt <| lt_of_eq_of_lt ha.symm hab)]
            exact h_lt_endpoint
          | n + 1 =>
            False.elim <| Nat.not_lt_zero n <| Nat.lt_of_succ_lt_succ <|
              Nat.lt_of_succ_lt_succ <| lt_of_lt_of_le
                (Nat.succ_lt_succ <| lt_of_eq_of_lt ha.symm hab) (Nat.succ_le_of_lt b.isLt)⟩)
      (fun (h_minimal : ¬@Minimal 𝒰 preorder.toLE Set.univ U) h_lt_endpoint ↦ by
        let ⟨y, hyU, hxy, hy, V, hyV, hVU⟩ := exists_lt_of_not_minimal U h_minimal x hx
        have ⟨R₀, hR₀⟩ := h_ind V hVU y hyV hy
        exact ⟨link hx hyU ++ R₀, by
          intro a b hab
          apply lt_of_eq_of_lt'
            (getElem_pts_append_right _ _ <| Nat.one_le_of_lt hab).symm
          let m := a.1
          match ha : m with
          | 0 =>
            subst m
            simp [ha]
            exact lt_of_lt_of_le hxy <| le_of_eq_of_le R₀.getElem_zero.symm <|
              hR₀.monotone <| Fin.mk_le_mk.mpr <| Nat.zero_le _
          | n + 1 =>
            subst m
            simp [ha]
            exact hR₀ <| Fin.mk_lt_mk.mpr <| Nat.lt_sub_of_add_lt <| lt_of_eq_of_lt ha.symm hab⟩))


theorem exists_bot_to_top [TopologicalSpace α] [CompleteLinearOrder α]
  [DenselyOrdered α] [OrderTopology α] [CompactSpace α] [Nontrivial α]
  (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ x : α, ∃ U ∈ 𝒰, x ∈ U) :
    ∃ R : Rollercoaster 𝒰 ⊥ ⊤, StrictMono R.points.get := by

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
      ∀ x ∈ U.1, ∃ y ∈ U.1, x < y ∧ y < ⊤ ∧ ∃ V, y ∈ V.1 ∧ (supOrder.lift Subtype.val).lt V U :=
    fun ⟨_, U, hU, rfl⟩ h_minimal x hx ↦
      let ⟨⟨V, hV, hV_nonempty⟩, _, ⟨hVt, rfl⟩, hsup⟩ :=
        Set.mem_iUnion.mp <| t_cover <| Set.mem_univ <| sSup U
      have h_lt_of_mem : ∀ x ∈ U.1, x < sSup U :=
        fun _ hmem ↦ lt_iff_le_and_ne.mpr ⟨le_sSup hmem,
          fun heq ↦ not_congr (top_mem_iff_minimal_t <| _) |>.mp h_minimal
            ((top_le_iff.mp <| @le_of_not_gt _ _ ⊤ (sSup U.1)
              (fun h_sSup_lt_top ↦
                let ⟨x, hx, hico⟩ := exists_Ico_subset_of_mem_nhds
                  (h_open ⟨U, U.2.1⟩ |>.mem_nhds <| heq ▸ hmem) ⟨⊤, h_sSup_lt_top⟩
                let ⟨y, hygt, hylt⟩ := DenselyOrdered.dense _ _ hx
                lt_iff_not_ge.mp hygt <| le_sSup <| hico <| Set.mem_Ico.mpr ⟨hygt.le, hylt⟩))
              ▸ heq ▸ hmem)⟩
      let ⟨_, hl, hlioc⟩ := exists_Ioc_subset_of_mem_nhds (h_open ⟨V, hV⟩ |>.mem_nhds hsup)
        ⟨_, h_lt_of_mem _ (Classical.choice U.2.2).2⟩
      let ⟨y, hy, hyl⟩ := lt_sSup_iff.mp <| max_lt hl <| h_lt_of_mem x hx
      have ⟨hy', hxy⟩ := max_lt_iff.mp hyl
      ⟨y, hy, hxy, lt_top_of_lt <| h_lt_of_mem y hy, ⟨V, ⟨V, hV, hV_nonempty⟩, hVt, rfl⟩,
        hlioc <| Set.mem_Ioc.mpr ⟨hy', le_sSup hy⟩, sSup U, hsup, h_lt_of_mem⟩

  choose _ x0 x1 using t_cover <| Set.mem_univ ⊥
  choose U x00 using x0
  cases x00
  choose _ x10 h_bot using x1
  choose hU x11 using x10
  cases x11

  obtain ⟨R', hR'⟩ := @exists_strictMono α t_set _ _ _ _ _ (supOrder.lift Subtype.val)
    ⊤ (top_mem_iff_minimal_t · |>.mp) exists_lt_of_not_minimal_t ⟨U, U, hU, rfl⟩ ⊥ h_bot bot_lt_top
  exact ⟨R'.map (m := id) (fun ⟨_, ⟨⟨U, hU, _⟩, _, rfl⟩⟩ ↦ ⟨U, hU, fun _ ⟨_, h, rfl⟩ ↦ h⟩),
    fun _ _ h ↦ by simp [map]; exact hR' h⟩





open unitInterval

variable [TopologicalSpace α]



def follows (π : C(I, α)) : Prop := ∃ i : Fin R.points.length → I,
  π ∘ i = R.points.get ∧
  StrictMono i ∧
  i ⟨0, R.len_pts_pos⟩ = 0 ∧
  i ⟨R.points.length - 1, Nat.pred_lt R.len_pts_ne_zero⟩ = 1 ∧
  ∀ (x : I) (n : Fin R.regions.length),
    i ⟨n, n.2.trans R.len_rgs_lt_len_pts⟩ ≤ x ∧
    x ≤ i ⟨n.succ, R.len_rgs_add_one_eq_len_pts ▸ Nat.succ_lt_succ n.2⟩ →
      π x ∈ R.regions[n].1



theorem not_follows_of_isTrivial (h_trivial : R.isTrivial) (π : Path a b) :
  ¬R.follows π :=
    fun ⟨_, _, _, h0, h1, _⟩ ↦ by
      have h : R.points.length - 1 = 0 := len_pts_eq_one_of_isTrivial h_trivial ▸ tsub_self _
      apply zero_ne_one' I <| h0.symm.trans <| congr_arg _ (Fin.mk_eq_mk.mpr h.symm) |>.trans h1



theorem exists_of_path (h_open : ∀ U : 𝒰, IsOpen U.1)
  (h_cover : ∀ x : α, ∃ U ∈ 𝒰, x ∈ U) (π : C(I, α)) :
    ∃ R : Rollercoaster 𝒰 (π 0) (π 1), R.follows π :=
  let 𝒰' : Set (Set I) := {U' | ∃ (U : 𝒰) (x : I), connectedComponentIn (π ⁻¹' U) x = U'}
  let ⟨R, hR⟩ := exists_bot_to_top (𝒰 := 𝒰')
    (fun ⟨_, U, x, rfl⟩ ↦ π.continuous.isOpen_preimage U (h_open U) |>.connectedComponentIn)
    (fun x ↦ let ⟨U, hU, hx⟩ := h_cover <| π x; ⟨_, ⟨⟨U, hU⟩, x, rfl⟩, mem_connectedComponentIn hx⟩)
  have hmap : ∀ U' : 𝒰', ∃ U ∈ 𝒰, ⇑π '' U' ⊆ U := fun ⟨_, ⟨U, h⟩, x, rfl⟩ ↦
    ⟨U, h, Set.image_subset_iff.mpr <| connectedComponentIn_subset (π ⁻¹' U) x⟩
  ⟨@map I 𝒰' 0 1 R α π 𝒰 hmap, (R.points[·]), funext (R.getElem_pts_map hmap · |>.symm),
    fun a b hab ↦ hR <| Fin.cast_lt_cast (R.length_map hmap) |>.mpr hab,
    by simp only [Fin.getElem_fin, getElem_zero]; rfl,
    by simp only [length_map, Fin.getElem_fin, getElem_len_pts_sub_one]; rfl,
    fun x n hx ↦ Set.mem_preimage.mp <| Set.image_subset_iff.mp (R.getElem_rgs_map hmap n) <|
      have hn : n < R.regions.length := lt_of_lt_of_eq n.2 <| R.len_rgs_map hmap
      have hOrdConnected : Set.OrdConnected <| R.regions[n]'hn |>.1 :=
        let ⟨_, _, _, rfl⟩ := R.regions[n]'hn; isPreconnected_connectedComponentIn.ordConnected
      hOrdConnected.out' (R.mem_rgs ⟨n, hn⟩) (R.succ_mem_rgs ⟨n, hn⟩) hx⟩



theorem exists_path_follows_of_pathConnected (h_pathConnected : ∀ U ∈ 𝒰, IsPathConnected U) :
    ¬R.isTrivial → ∃ π : Path a b, R.follows π := by

  apply R.induction_take
  · exact (False.elim <| · isTrivial_trivial)
  · have h := fun (i : Fin R.regions.length) ↦
      (h_pathConnected R.regions[i] R.regions[i].2).joinedIn
        (R.points[i]'sorry) (R.mem_rgs i) (R.points[i.succ]'sorry) (R.succ_mem_rgs i)
    intro n hn h_ind h_nontrivial
    have hn' : n < R.points.length - 1 := sorry
    let ⟨π₀, hπ₀⟩ := h ⟨n, lt_of_eq_of_lt' R.len_rgs_eq_len_pts_sub_one.symm hn'⟩
    by_cases h_isTrivial_take : (R.take hn').isTrivial
    · have hn0 : n = 0 := sorry
      cases hn0
      use π₀.cast R.getElem_zero.symm rfl
      use fun ⟨x, _⟩ ↦ ⟨x, sorry, sorry⟩
      split_ands
      · apply funext
        intro ⟨x, hx⟩
        have hle : x ≤ 1 := Nat.le_of_lt_succ <| lt_of_eq_of_lt' (len_pts_take _) hx
        match x with
          | 0 => simp
          | x + 1 => simp [take, eq_of_le_of_ge hle <| Nat.le_add_left 1 x]
      · intro _ _ hlt; simp [Fin.mk_lt_mk.mp hlt]
      · simp
      · simp
      · intro x ⟨_, h⟩ _; simp at h; simp [take, h]; exact hπ₀ x
    ·
      let ⟨π₁, i, _, _, hi0, hi1, _⟩ := h_ind h_isTrivial_take

      use π₁.trans <| π₀.cast rfl rfl
      use fun ⟨x, _⟩ ↦ if x = n + 1 then 1 else ⟨(i ⟨x, sorry⟩).1 / 2, sorry⟩
      simp only
      split_ands
      · sorry
      · intro ⟨a, _⟩ ⟨b, hb⟩ hlt
        simp at hb hlt ⊢
        simp [(lt_of_lt_of_le hlt <| Nat.le_of_lt_succ hb).ne]
        apply Subtype.coe_lt_coe.mp
        --#check

        sorry
      · simp [hi0]
      · simp
      · sorry







variable {T : α → Type*}
variable (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)



def rel (f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1)
  (R1 R2 : Rollercoaster 𝒰 a b) : Prop :=
    R1.jumpAll f = R2.jumpAll f



variable (h_open : ∀ U : 𝒰, IsOpen U.1) (h_cover : ∀ a : α, ∃ U : 𝒰, a ∈ U.1)

variable {f : {U : 𝒰} → (p : U.1) → (q : U.1) → T p.1 → T q.1}
variable (f_id : ∀ {U : 𝒰} (p : U.1), f p p = id)
variable (f_trans : ∀ {U : 𝒰} (p q r : U.1), f q r ∘ f p q = f p r)
variable (f_inter : ∀ {U V : 𝒰} {p q : α} (hpU : p ∈ U.1) (hpV : p ∈ V.1)
  (hqU : q ∈ U.1) (hqV : q ∈ V.1), f ⟨p, hpU⟩ ⟨q, hqU⟩ = f ⟨p, hpV⟩ ⟨q, hqV⟩)





theorem rel_of_homotopic {π₀ π₁ : Path a b} (φ : Path.Homotopic π₀ π₁)
  {R₀ : Rollercoaster 𝒰 a b} (h_follows_0 : R.follows π₀)
  {R₁ : Rollercoaster 𝒰 a b} (h_follows_1 : R₁.follows π₁) :
    R₀.jumpAll f = R₁.jumpAll f := sorry


#check Path.Homotopy



end Rollercoaster
