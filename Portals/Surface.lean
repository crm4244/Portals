import Portals.Side

variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X]



namespace Surface




class PreRealizer (S : Set X) (p : X) where
  set : Set X
  isOpen : IsOpen set
  origin_mem : p ∈ set



namespace PreRealizer


variable {S : Set X} {p : X}


def toComponent (PR : PreRealizer S p) : (Side.center' S)⁻¹' PR.set → Set X :=
  fun a ↦ a.1.toComponent PR.isOpen a.2

def toComponent_at_origin (PR : PreRealizer S p) : (Side.center' S)⁻¹' {p} → Set X :=
  fun a ↦ PR.toComponent ⟨a.1, Set.mem_preimage.mpr (Eq.subst (Eq.symm a.2) PR.origin_mem)⟩


end PreRealizer




class Realizer (S : Set X) (p : X) where
  preRealizer : PreRealizer S p
  bijective_toComponent_of_center_eq_origin :
    Function.Bijective preRealizer.toComponent_at_origin



namespace Realizer


variable {S : Set X} {p : X} {hp : p ∈ S}

def set (R : Realizer S p) : Set X := R.preRealizer.set
def isOpen (R : Realizer S p) : IsOpen R.set := R.preRealizer.isOpen
def origin_mem (R : Realizer S p) : p ∈ R.set := R.preRealizer.origin_mem

def toComponent (R : Realizer S p) : (Side.center' S)⁻¹' R.set → Set X :=
  R.preRealizer.toComponent

def toComponent_at_origin (R : Realizer S p) : (Side.center' S)⁻¹' {p} → Set X :=
  R.preRealizer.toComponent_at_origin

noncomputable def equiv_toComponent_of_center_eq_origin (R : Realizer S p) :=
  Equiv.ofBijective R.toComponent_at_origin R.bijective_toComponent_of_center_eq_origin

noncomputable def fromComponent (R : Realizer S p) : Set X → (Side.center' S)⁻¹' {p} :=
  R.equiv_toComponent_of_center_eq_origin.invFun


theorem inverse_fromComponent_left (R : Realizer S p) :
    Function.LeftInverse R.fromComponent R.toComponent_at_origin :=
  R.equiv_toComponent_of_center_eq_origin.left_inv

theorem inverse_fromComponent_right (R : Realizer S p) :
    Function.RightInverse R.fromComponent R.toComponent_at_origin :=
  R.equiv_toComponent_of_center_eq_origin.right_inv


noncomputable def toOrigin (R : Realizer S p) :
  (Side.center' S)⁻¹' R.set → (Side.center' S)⁻¹' {p} := R.fromComponent ∘ R.toComponent


end Realizer



end Surface





class Surface (S : Set X) where
  surjective_center : Function.Surjective (fun a : Side S ↦ a.center)
  realizer (p : X) : Surface.Realizer S p





namespace Surface


variable {S : Set X}


-- theorem: nondegenerate portals have closed surfaces
-- theorem: any open neighborhood of p ∈ S has a realizer subset


theorem interior_eq_empty (hS : Surface S) : interior S = ∅ := sorry


/-


-- these hold for nondegenerate portals
theorem frontier_eq_self (hS : Surface S) : frontier S = S := by
  rw [frontier, hS.interior_eq_empty, Set.diff_empty]
  exact closure_eq_iff_isClosed.mpr hS.1

theorem closure_eq_self (hS : Surface S) : closure S = S :=
  IsClosed.closure_eq (hS.isClosed)


theorem IsOpen_compl (hS : Surface S) : IsOpen Sᶜ := isOpen_compl_iff.mpr hS.1

theorem IsOpen_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) : IsOpen (U \ S) :=
  IsOpen.sdiff hU (IsClosed hS)
-/

theorem inter_closure_subset_frontier_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ closure U ⊆ frontier (U \ S) := by
  intro p ⟨hpS, hpU⟩
  unfold frontier
  rw [Set.mem_diff]
  split_ands
  · apply mem_closure_iff.mpr
    intro V hV hpV
    rw [← compl_compl S, Set.diff_compl, ← Set.inter_assoc]
    rw [← Set.diff_compl, compl_compl]
    apply Set.nonempty_of_not_subset
    intro hVU
    have hVUi := (IsOpen.subset_interior_iff (IsOpen.inter hV hU)).mpr hVU
    rw [hS.interior_eq_empty] at hVUi
    exact Set.nonempty_iff_ne_empty.mp
      (mem_closure_iff.mp hpU V hV hpV)
      (Set.subset_empty_iff.mp hVUi)
  · exact fun h ↦ ((Set.mem_diff p).mp (interior_subset h)).2 hpS


theorem inter_closure_subset_closure_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ closure U ⊆ closure (U \ S) := fun p ⟨hpS, hpU⟩ ↦
  frontier_subset_closure (
    inter_closure_subset_frontier_diff hS hU (
      (Set.mem_inter_iff p S (closure U)).mpr ⟨hpS, hpU⟩))


theorem inter_subset_closure_diff (hS : Surface S) {U : Set X} (hU : IsOpen U) :
    S ∩ U ⊆ closure (U \ S) := fun p ⟨hpS, hpU⟩ ↦
  frontier_subset_closure (
    inter_closure_subset_frontier_diff hS hU (
      (Set.mem_inter_iff p S (closure U)).mpr ⟨hpS, subset_closure hpU⟩))


/-
  Let U be an open set and p ∈ S have p ∈ cl(U).
  Suppose U / S has finitely many connected components.
  Then there is a connected component C of U \ S with p ∈ cl(C).
-/
theorem inter_closure_subset_cmpnts_closure (hS : Surface S) {U : Set X} (hU : IsOpen U)
    (hUSC_fin : Finite (components (U \ S))) :
    S ∩ closure U ⊆ ⋃ C ∈ components (U \ S), closure C := by
  intro p hpScU
  have hpUS : p ∈ closure (U \ S) := inter_closure_subset_closure_diff hS hU (
    (Set.mem_inter_iff p S (closure U)).mpr hpScU)
  rw [← sUnion_cmpnts (U \ S), Set.Finite.closure_sUnion hUSC_fin] at hpUS
  exact hpUS



end Surface
