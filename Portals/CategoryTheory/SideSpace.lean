import Portals.CategoryTheory.EtaleSpace
import Portals.Legacy.Basic


-- Here's an outline of the things i need to write


-- Define the components presheaf
-- define sidespace of a TopCat morphism as etalespace of the sheafifcation
-- sidesspace as a functor Top ↓ Top → Top
-- projection into components
-- commutativity of stuff

-- portal maps can be its own short file with just the definition. Maybe unneccesary

-- for another file:
-- component realizing function φ
-- component realizers as discrete fibrations
-- portal maps preserve component realizers
-- do component realizers form a subcategory / subfunctor?
-- component transport function τ = φₚ⁻¹ ∘ φₐq

-- for later:
-- gluing pattern on an arbitrary group
-- transitivity
-- local consistency
-- the other local condition about unique representation
-- groupoid form
-- Material space as the orbitspace of the groupoid

-- the union surface
-- the recommendation maps
-- commutativity of τ and π. What was π again?

-- the composition gluing pattern
-- transitivity
-- local consistency
-- etc

-- the equality gluing pattern
-- transitivity
-- local consistency
-- etc

open Topology TopologicalSpace CategoryTheory Opposite TopCat


#check connectedComponentIn_lemma_3
#check components
#check ConnectedComponents


-- build the category of connected subsets of X





def ComponentsPresheaf {X S : TopCat} (i : S ⟶ X) : (Opens X)ᵒᵖ ⥤ Set (Set X) :=
  let componentSubsets (U : (Opens X)ᵒᵖ) : Set (Set X) :=
    { Subtype.val '' (ConnectedComponents.mk ⁻¹' {C}) |
      C : ConnectedComponents (U.unop.1 \ Set.range i.hom.toFun : Set X) }

  have f V U : componentSubsets V → True := by
    unfold componentSubsets
    intro ⟨C, hC⟩
    simp only [Set.mem_setOf_eq] at hC

    rcases hC with ⟨⟨x, b⟩, rfl⟩
    sorry
  {
    obj := componentSubsets
    map := Lean.IR.Sorry.State.mk.noConfusion
    map_id := sorry
    map_comp := sorry
  }

  by
      intro V U j

        -- use Classical.choose

        sorry
      exact sorry -- turn f into a morphism of sets
