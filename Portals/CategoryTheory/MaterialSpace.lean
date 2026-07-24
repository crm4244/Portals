import Portals.CategoryTheory.Recommendations
import Portals.CategoryTheory.GeneralizedMultiset


universe u v



namespace Portal



variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {F : Set (PortalMap Y X)}




section transport


noncomputable def pretransport (P : Equiv.Perm F) (f : F) :
  f.1.range → X := ((P f).1 <| f.1.inv_range ·)


variable (pretransport_symmetry : ∀ P (f g : F) (q : X) (hf : q ∈ f.1.range) (hg : q ∈ g.1.range),
  pretransport P f ⟨q, hf⟩ = pretransport P g ⟨q, hg⟩)

def 𝒰 (F : Set (PortalMap Y X)) : Set X := ⋃ f : F, f.1.range

#check fun P ↦ Set.iUnionLift (fun f : F ↦ f.1.range) (pretransport P)
  (pretransport_symmetry P) _ subset_rfl



noncomputable def transport (P : Equiv.Perm F) (x : 𝒰 F) : 𝒰 F :=
  ⟨Set.iUnionLift _ _ (pretransport_symmetry P) _ subset_rfl x,
    match Set.mem_iUnion.mp x.2 with
    | ⟨_, h⟩ => Set.iUnionLift_of_mem (hT := subset_rfl) x h ▸
      Set.mem_iUnion_of_mem _ (Set.mem_range_self _)⟩


end transport




variable {S : Set Y} (γ : GluingPattern S (Equiv.Perm F))
variable (Γ : GeneralizedMultiset (Equiv.Perm F) → Equiv.Perm F)



noncomputable def quattle {p : X} (a b : Sides.at_point (𝒮 F S) p) :
  GeneralizedMultiset (Equiv.Perm F) :=
    GeneralizedMultiset.of_map fun f : relevant_portal_maps F p ↦
      recommendation_map γ (p := ⟨p, f.2⟩) a b


variable (𝒢_trans : ∀ {p : X} (a b c : Sides.at_point (𝒮 F S) p),
  Γ (quattle γ a b) * Γ (quattle γ b c) = Γ (quattle γ a c))



noncomputable def combinedGluingPattern : GluingPattern (𝒮 F S) (Equiv.Perm F) :=
  { map a b := Γ (quattle γ a b), trans := 𝒢_trans }

noncomputable abbrev 𝒢 := combinedGluingPattern γ Γ 𝒢_trans

variable (𝒢_isLocallyConsistent : GluingPattern.isLocallyConsistent (𝒢 γ Γ 𝒢_trans))





end Portal
