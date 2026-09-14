
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.ConcreteCategory.Basic

universe w v u

open CategoryTheory

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)]
variable [ConcreteCategory C FC]


#check ConcreteCategory Cᵒᵖ (fun X Y ↦ FC Y.unop X.unop)
