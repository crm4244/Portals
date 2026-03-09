

import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.Topology.Sheaves.Init
import Mathlib.Data.Set.Subsingleton

/-!
# Precosheaves on a topological space

This is based on the code from Mathlib\Topology\Sheaves\Precosheaf.lean
-/

universe w v u

open CategoryTheory TopologicalSpace Opposite Functor

variable (C : Type u) [Category.{v} C]

namespace TopCat

/-- The category of `C`-valued precosheaves on a (bundled) topological space `X`. -/
def Precosheaf (X : TopCat.{w}) : Type max u v w :=
  Opens X ⥤ C

instance (X : TopCat.{w}) : Category (Precosheaf.{w, v, u} C X) :=
  inferInstanceAs (Category (Opens X ⥤ C : Type max u v w))

variable {C}

namespace Precosheaf

@[simp] theorem comp_app {X : TopCat} {U : Opens X} {P Q R : Precosheaf C X}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    (f ≫ g).app U = f.app U ≫ g.app U := rfl

@[ext]
lemma ext {X : TopCat} {P Q : Precosheaf C X} {f g : P ⟶ Q}
    (w : ∀ U : Opens X, f.app U = g.app U) :
    f = g := by
  apply NatTrans.ext
  ext U
  induction U with | _ U => ?_
  apply w

/-- attribute `cosheaf_restrict` to mark lemmas related to restricting sheaves -/
macro "cosheaf_restrict" : attr =>
  `(attr|aesop safe 50 apply (rule_sets := [$(Lean.mkIdent `Restrict):ident]))

attribute [cosheaf_restrict] bot_le le_top le_refl inf_le_left inf_le_right
  le_sup_left le_sup_right

/-- `restrict_tac` solves relations among subsets (copied from `aesop cat`) -/
macro (name := restrict_tac) "restrict_tac" c:Aesop.tactic_clause* : tactic =>
`(tactic| first | assumption |
  aesop $c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false })
    (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

/-- `restrict_tac?` passes along `Try this` from `aesop` -/
macro (name := restrict_tac?) "restrict_tac?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false
                 maxRuleApplications := 300 })
  (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

attribute[aesop 10% (rule_sets := [Restrict])] le_trans
attribute[aesop safe destruct (rule_sets := [Restrict])] Eq.trans_le
attribute[aesop safe -50 (rule_sets := [Restrict])] Aesop.BuiltinRules.assumption

example {X} [CompleteLattice X] (v : Nat → X) (w x y z : X) (e : v 0 = v 1) (_ : v 1 = v 2)
    (h₀ : v 1 ≤ x) (_ : x ≤ z ⊓ w) (h₂ : x ≤ y ⊓ z) : v 0 ≤ y := by
  restrict_tac

variable {X : TopCat} {C : Type*} [Category C] {FC : C → C → Type*} {CC : C → Type*}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj V`, we provide the notation `x |_ₕ i` (`h` stands for `hom`) for `i : V ⟶ U`,
and the notation `x |_ₗ U ⟪i⟫` (`l` stands for `le`) for `i : V ≤ U`.
-/
def restrict {F : X.Precosheaf C}
    {V : Opens X} (x : ToType (F.obj V)) {U : Opens X} (h : V ⟶ U) : ToType (F.obj U) :=
  F.map h x

/-- restriction of a section along an inclusion -/
scoped[AlgebraicGeometry] infixl:80 " |_ₕ " => TopCat.Precosheaf.restrict
/-- restriction of a section along a subset relation -/
scoped[AlgebraicGeometry] notation:80 x " |_ₗ " U " ⟪" e "⟫ " =>
  @TopCat.Precosheaf.restrict _ _ _ _ _ _ _ _ _ x U (@homOfLE (Opens _) _ _ U e)

open AlgebraicGeometry

/-- The restriction of a section along an inclusion of open sets.
For `x : F.obj V`, we provide the notation `x |_ U`, where the proof `V ≤ U` is inferred by
the tactic `Top.precosheaf.restrict_tac'` -/
abbrev restrictOpen {F : X.Precosheaf C}
    {V : Opens X} (x : ToType (F.obj V)) (U : Opens X)
    (e : V ≤ U := by restrict_tac) :
    ToType (F.obj U) :=
  x |_ₗ U ⟪e⟫

/-- restriction of a section to open subset -/
scoped[AlgebraicGeometry] infixl:80 " |_ " => TopCat.Precosheaf.restrictOpen

theorem restrict_restrict
    {F : X.Precosheaf C} {U V W : Opens X} (e₁ : V ≤ U) (e₂ : W ≤ V) (x : ToType (F.obj W)) :
    x |_ V |_ U = x |_ U := by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem map_restrict
    {F G : X.Precosheaf C} (e : F ⟶ G) {U V : Opens X} (h : V ≤ U) (x : ToType (F.obj V)) :
    e.app _ (x |_ U) = e.app _ x |_ U := by
  delta restrictOpen restrict
  rw [← ConcreteCategory.comp_apply, NatTrans.naturality, ConcreteCategory.comp_apply]

open CategoryTheory.Limits

variable (C)

/-- The pushforward functor. -/
@[simps!]
def pushforward {X Y : TopCat.{w}} (f : X ⟶ Y) : X.Precosheaf C ⥤ Y.Precosheaf C :=
  (whiskeringLeft _ _ _).obj (Opens.map f)

/-- push forward of a precosheaf -/
scoped[AlgebraicGeometry] notation f:80 " _* " P:81 =>
  Functor.obj (TopCat.Precosheaf.pushforward _ f) P

@[simp]
theorem pushforward_map_app' {X Y : TopCat.{w}} (f : X ⟶ Y) {ℱ 𝒢 : X.Precosheaf C} (α : ℱ ⟶ 𝒢)
    {U : Opens Y} : ((pushforward C f).map α).app U = α.app ((Opens.map f).obj U) :=
  rfl

lemma id_pushforward (X : TopCat.{w}) : pushforward C (𝟙 X) = 𝟭 (X.Precosheaf C) := rfl

variable {C}

namespace Pushforward

/-- The natural isomorphism between the pushforward of a precosheaf along the identity continuous
map and the original precosheaf. -/
def id {X : TopCat.{w}} (ℱ : X.Precosheaf C) : 𝟙 X _* ℱ ≅ ℱ := Iso.refl _

@[simp]
theorem id_hom_app {X : TopCat.{w}} (ℱ : X.Precosheaf C) (U) : (id ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
theorem id_inv_app {X : TopCat.{w}} (ℱ : X.Precosheaf C) (U) :
    (id ℱ).inv.app U = 𝟙 _ := rfl

theorem id_eq {X : TopCat.{w}} (ℱ : X.Precosheaf C) : 𝟙 X _* ℱ = ℱ := rfl

/-- The natural isomorphism between
the pushforward of a precosheaf along the composition of two continuous maps and
the corresponding pushforward of a pushforward. -/
def comp {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Precosheaf C) :
    (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) := Iso.refl _

theorem comp_eq {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Precosheaf C) :
    (f ≫ g) _* ℱ = g _* (f _* ℱ) :=
  rfl

@[simp]
theorem comp_hom_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Precosheaf C) (U) :
    (comp f g ℱ).hom.app U = 𝟙 _ := rfl

@[simp]
theorem comp_inv_app {X Y Z : TopCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Precosheaf C) (U) :
    (comp f g ℱ).inv.app U = 𝟙 _ := rfl

end Pushforward

/--
An equality of continuous maps induces a natural isomorphism between the pushforwards of a
precosheaf along those maps.
-/
def pushforwardEq {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Precosheaf C) :
    f _* ℱ ≅ g _* ℱ :=
  isoWhiskerRight ((Opens.mapIso f g h)) ℱ

theorem pushforward_eq' {X Y : TopCat.{w}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.Precosheaf C) :
    f _* ℱ = g _* ℱ := by rw [h]

@[simp]
theorem pushforwardEq_hom_app {X Y : TopCat.{w}} {f g : X ⟶ Y}
    (h : f = g) (ℱ : X.Precosheaf C) (U) :
    (pushforwardEq h ℱ).hom.app U = ℱ.map (eqToHom (by cat_disch)) := by
  simp [pushforwardEq]

variable (C)

section Iso

/-- A homeomorphism of spaces gives an equivalence of categories of precosheaves. -/
@[simps!]
def precosheafEquivOfIso {X Y : TopCat} (H : X ≅ Y) : X.Precosheaf C ≌ Y.Precosheaf C :=
  Equivalence.congrLeft (Opens.mapMapIso H).symm

variable {C}

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def toPushforwardOfIso {X Y : TopCat} (H : X ≅ Y) {ℱ : X.Precosheaf C} {𝒢 : Y.Precosheaf C}
    (α : H.hom _* ℱ ⟶ 𝒢) : ℱ ⟶ H.inv _* 𝒢 :=
  (precosheafEquivOfIso _ H).toAdjunction.homEquiv ℱ 𝒢 α

@[simp]
theorem toPushforwardOfIso_app {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : X.Precosheaf C} {𝒢 : Y.Precosheaf C}
    (H₂ : H₁.hom _* ℱ ⟶ 𝒢) (U : Opens X) :
    (toPushforwardOfIso H₁ H₂).app U =
      ℱ.map (eqToHom (by simp [Opens.map, Set.preimage_preimage])) ≫
        H₂.app ((Opens.map H₁.inv).obj U) := by
  simp [toPushforwardOfIso, Adjunction.homEquiv_unit]

/-- If `H : X ≅ Y` is a homeomorphism,
then given an `H _* ℱ ⟶ 𝒢`, we may obtain an `ℱ ⟶ H ⁻¹ _* 𝒢`.
-/
def pushforwardToOfIso {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : Y.Precosheaf C} {𝒢 : X.Precosheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) : H₁.inv _* ℱ ⟶ 𝒢 :=
  ((precosheafEquivOfIso _ H₁.symm).toAdjunction.homEquiv ℱ 𝒢).symm H₂

@[simp]
theorem pushforwardToOfIso_app {X Y : TopCat} (H₁ : X ≅ Y) {ℱ : Y.Precosheaf C} {𝒢 : X.Precosheaf C}
    (H₂ : ℱ ⟶ H₁.hom _* 𝒢) (U : Opens X) :
    (pushforwardToOfIso H₁ H₂).app U =
      H₂.app ((Opens.map H₁.inv).obj U) ≫
        𝒢.map (eqToHom (by simp [Opens.map, Set.preimage_preimage])) := by
  simp [pushforwardToOfIso, Equivalence.toAdjunction, Adjunction.homEquiv_counit]

end Iso

variable [HasColimits C]

noncomputable section

/-- Pullback a precosheaf on `Y` along a continuous map `f : X ⟶ Y`, obtaining a precosheaf
on `X`. -/
def pullback {X Y : TopCat.{v}} (f : X ⟶ Y) : Y.Precosheaf C ⥤ X.Precosheaf C :=
  (Opens.map f).lan

/-- The pullback and pushforward along a continuous map are adjoint to each other. -/
def pushforwardPullbackAdjunction {X Y : TopCat.{v}} (f : X ⟶ Y) :
    pullback C f ⊣ pushforward C f :=
  Functor.lanAdjunction _ _

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
def pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.hom)
    (precosheafEquivOfIso C H.symm).toAdjunction

/-- Pulling back along the inverse of a homeomorphism is the same as pushing forward along it. -/
def pullbackInvIsoPushforwardHom {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.inv ≅ pushforward C H.hom :=
  Adjunction.leftAdjointUniq (pushforwardPullbackAdjunction C H.inv)
    (precosheafEquivOfIso C H).toAdjunction

variable {C}

/-
/-- If `f '' U` is open, then `f⁻¹ℱ U ≅ ℱ (f '' U)`. -/
def pullbackObjObjOfImageOpen {X Y : TopCat.{v}} (f : X ⟶ Y) (ℱ : Y.Precosheaf C) (U : Opens X)
    (H : IsOpen (f '' SetLike.coe U)) : ((pullback C f).obj ℱ).obj U ≅ ℱ.obj ⟨_, H⟩ := by
  let x : CostructuredArrow (Opens.map f) U := CostructuredArrow.mk
    (@homOfLE _ _ ((Opens.map f).obj ⟨_, H⟩) (Set.image_preimage.le_u_l _))
  have hx : IsTerminal x :=
    { lift := fun s ↦ by
        fapply CostructuredArrow.homMk
        · change op (unop _) ⟶ op (⟨_, H⟩ : Opens _)
          refine (homOfLE ?_).op
          apply (Set.image_mono s.pt.hom.unop.le).trans
          exact Set.image_preimage.l_u_le (SetLike.coe s.pt.left.unop)
        · simp [eq_iff_true_of_subsingleton] }
  exact IsColimit.coconePointUniqueUpToIso
    ((Opens.map f).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit ℱ U)
    (colimitOfDiagramTerminal hx _)
-/

end

end Precosheaf

end TopCat
