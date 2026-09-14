import Portals.GluingPattern


variable {X : Type} [hX : TopologicalSpace X] [hX2 : T2Space X]
  {S : Set X} [hS : Surface S] {F : Set (PortalMap S)}


def SS : Set X := ⋃ f ∈ F, f.map '' (Subtype.val ⁻¹' S)

variable [hSS : @Surface _ _ hX2 SS]


--def gluingpatternequivalencerelation_wellDefined (p : X) (a b : (Side.center' SS)⁻¹' {p})
  --{f g : F} (hf : p ∈ Set.range f.map) (hg : p ∈ Set.range g.map) : Prop := sorry
    -- γ (f⁻¹ a) (f⁻¹ b) = γ (g⁻¹ a) (g⁻¹ b)
    -- need to define the inverse lift of a portalmap

--def gluingpatternequivalencerelation (a b : Side SS) : Prop := a = b ∨ ∀ f g : F,
  --a.center ∈ Set.range f.map → b.center ∈ Set.range g.map → γ (f⁻¹ a) (g⁻¹ b) f = g
