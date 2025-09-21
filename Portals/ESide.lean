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


/-
  Claim: If P ∈ S has the sequence C[n] ∈ sides(P, O[n]) then Intersection(cl(C[n])) = {P}.

  Proof. For every n, since C[n+1] ⊆ C[n], cl(C[n+1]) ⊆ cl(C[n]).
  Let m>0 and suppose that cl(C[n+1]) = cl(C[n]) for all n>m.
  Then by induction every n>=m has cl(C[m]) = cl(C[n-1]) ⊆ cl(O[n-1]) ⊆ O[n].
  By induction again, every n<m has cl(C[m]) ⊆ cl(O[m]) ⊆ O[n].
  So, C[m] ⊆ Intersection(O[n]) = {P} ⊆ S.
  But, C[m] was constructed as a nonempty subset of O[n] \ S.
  Contradiction. We must instead have an infinite number of n’s with cl(C[n+1]) ⊂ cl(C[n]).
  Note cl(C[n]) is compact since it is a closed subset of the compact set cl(O[n]).
  We may now apply Cantor’s Intersection Theorem to see that Intersection(cl(C[n])) is nonempty.
  Let Q ∈ Intersection(cl(C[n])). Then for every n>0 we have Q ∈ cl(C[n+1]) ⊆ cl(O[n+1]) ⊆ O[n].
  So, Q ∈ Intersection(O[n]) = {P}. So, Q = P.

  QED
-/
theorem isCenter_iff_isCenter_generator (ha : ESide S a) (p : X) {E} (hE : IsGenerator S a E) :
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


theorem nested (ha : ESide S a) {n m : ℕ} (h : n ≤ m) : a m ⊆ a n := by
  --induction
  sorry


end ESide



theorem Encapsulation.isCenter_ESide_center (ha : ESide S a) {E} (hE : ESide.IsGenerator S a E) :
    Encapsulation.isCenter E (ESide.center ha) :=
  (ha.isCenter_iff_isCenter_generator ha.center hE).mp (ESide.isCenter_center ha)
