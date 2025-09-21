import Portals.Encapsulation
import Portals.Basic



variable {X : Type} [hX : TopologicalSpace X]


class ESide.IsGenerator (S : Set X) (a : ℕ → Set X) (E : ℕ → Set X) where
  isEncapsulation : Encapsulation E
  nth_componentIn : ∀ n, a n ∈ components ((E n) \ S)


class ESide (S : Set X) (a : ℕ → Set X) where
  exists_generator : ∃ E, ESide.IsGenerator S a E
  nth_nested (n : ℕ) : a (n + 1) ⊆ a n


def ESide.isCenter (a : ℕ → Set X) (p : X) := ∀ n, p ∈ closure (a n)


variable {S : Set X} {a : ℕ → Set X}



namespace ESide



theorem isCenter_iff_isCenter_generator (ha : ESide S a) (p : X) {E} (_ : IsGenerator S a E) :
    isCenter a p ↔ Encapsulation.isCenter E p := by
  sorry


theorem center_exists (ha : ESide S a) : ∃ p, isCenter a p :=
  match ha.exists_generator with
    | ⟨_, hE⟩ => match hE.isEncapsulation.center_exists with
      | ⟨p, hpE⟩ => ⟨p, (isCenter_iff_isCenter_generator ha p hE).mpr hpE⟩


theorem center_unique (ha : ESide S a) : ∀ p, isCenter a p → ∀ q, isCenter a q → p=q := by
  rcases ha.exists_generator with ⟨E, hE⟩
  intro p hp q hq
  have f := fun r hr => (isCenter_iff_isCenter_generator ha r hE).mp hr
  exact hE.isEncapsulation.center_unique (f p hp) (f q hq)


theorem center_exists_unique (ha : ESide S a) : ∃! p, isCenter a p :=
  match center_exists ha with | ⟨p, hp⟩ => ⟨p, ⟨hp, fun q hq => center_unique ha q hq p hp⟩⟩


noncomputable def center (ha : ESide S a) := Classical.choose (center_exists ha)


theorem isCenter_center (ha : ESide S a) : isCenter a (center ha) :=
  Classical.choose_spec (center_exists ha)



end ESide



theorem Encapsulation.isCenter_ESide_center (ha : ESide S a) {E} (hE : ESide.IsGenerator S a E) :
    Encapsulation.isCenter E (ESide.center ha) :=
  (ha.isCenter_iff_isCenter_generator ha.center hE).mp (ESide.isCenter_center ha)
