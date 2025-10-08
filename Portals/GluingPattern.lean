import Portals.PortalMap


variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X] {S : Set X} [hS : Surface S]



noncomputable def GluingPattern.toOrigin {p : X} {realizer : Surface.Realizer S p} {r : X}
    (h : r ∈ realizer.set) (a : (Side.center' S) ⁻¹' {r}) :=
  (realizer.toOrigin ⟨a.1, Set.mem_preimage.mpr (Eq.symm (
    Set.mem_singleton_iff.mp (Set.mem_preimage.mp a.2)) ▸ h)⟩)


class GluingPattern (F : Set (PortalMap S)) where
  map (p : X) : (Side.center' S)⁻¹' {p} → (Side.center' S)⁻¹' {p} → F → F
  map_bijective (p : X) : ∀ a b, Function.Bijective (map p a b)
  trans (p : X) : ∀ a b c, map p b c ∘ map p a b = map p a c
  realizer (p : X) : Surface.Realizer S p
  local_consistency_inter {p q r : X} (hr : r ∈ (realizer p).set ∩ (realizer q).set) :
    ∀ a b : (Side.center' S)⁻¹' {r},
      map p (GluingPattern.toOrigin hr.1 a) (GluingPattern.toOrigin hr.1 b) =
      map q (GluingPattern.toOrigin hr.2 a) (GluingPattern.toOrigin hr.2 b)




variable {F : Set (PortalMap S)}



namespace GluingPattern




theorem local_consistency (γ : GluingPattern F) (p : X) {q : X} (hq : q ∈ (γ.realizer p).set) :
  ∀ a b : (Side.center' S)⁻¹' {q},
    γ.map p (GluingPattern.toOrigin hq a) (GluingPattern.toOrigin hq b) = γ.map q a b := sorry


theorem refl_eq_id (γ : GluingPattern F) (p : X) :
    ∀ a, γ.map p a a = id := sorry
  -- follows from transitivity


theorem comm_eq_inv_left (γ : GluingPattern F) (p : X) :
    ∀ a b, Function.LeftInverse (γ.map p a b) (γ.map p b a) := sorry
  -- follows from transitivity


theorem comm_eq_inv_right (γ : GluingPattern F) (p : X) :
    ∀ a b, Function.RightInverse (γ.map p a b) (γ.map p b a) :=
  fun a b ↦ comm_eq_inv_left γ p b a



end GluingPattern
