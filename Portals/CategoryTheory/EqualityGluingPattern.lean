import Portals.CategoryTheory.Recommendations




namespace Portal


variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
variable {S : Set Y}
variable {F : Set (PortalMap Y X)}


def recommendations_agree (γ : GluingPattern S (Equiv.Perm F)) {a b : Sides (union_surface S F)}
  (hab : a.center = b.center) (f g : relevant F a.center) : Prop :=
    recommendation_map γ hab f.2 = recommendation_map γ hab g.2


#check Quotient
open Classical in noncomputable def equalityGluingPattern (γ : GluingPattern S (Equiv.Perm F)) :
    GluingPattern (union_surface S F) (Equiv.Perm F) where
  map {a _} hab := if h_nonempty : Nonempty (relevant F a.center) then
    Quot.lift (fun f : relevant F a.center ↦ recommendation_map γ hab f.2) (fun _ _ x ↦ x)
      (@default _ (@Quot.instInhabited_mathlib _ (recommendations_agree γ hab)
        (inhabited_of_nonempty h_nonempty))) else 1
  trans {a _ _} hab hbc := by
    simp?
    -- this seems false
    -- maybe this construction is just wrong

    sorry


end Portal
