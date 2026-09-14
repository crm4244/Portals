import Mathlib.Logic.Equiv.Basic

universe u v



class GenMulti (α : Type u) where
  index : Type v
  val : index → α



namespace GenMulti

variable {α : Type u} {a b c : GenMulti α}


def of_function {β : Type v} (f : β → α) : GenMulti α := {index := β, val := f}


def rel (a b : GenMulti α) : Prop :=
  ∃ e : a.index ≃ b.index, a.val = b.val ∘ e

theorem rel_refl (a : GenMulti α) : rel a a :=
  ⟨Equiv.refl a.index, rfl⟩

theorem rel_symm : rel a b → rel b a :=
  fun ⟨e, _⟩ ↦ ⟨e.symm, by aesop⟩

theorem rel_trans : rel a b → rel b c → rel a c :=
  fun ⟨e₁, _⟩ ⟨e₂, _⟩ ↦ ⟨e₁.trans e₂, by aesop⟩

instance : Equivalence <| @rel α where
  refl := rel_refl
  symm := rel_symm
  trans := rel_trans

instance (α : Type u) : Setoid (GenMulti α) where
  r := rel
  iseqv := instEquivalenceRel


end GenMulti




def GeneralizedMultiset (α : Type u) : Type max u (v + 1) :=
  Quotient (GenMulti.instSetoid.{u, v} α)


variable {α : Type u}

def GeneralizedMultiset.of_function {β : Type v} (f : β → α) :
  GeneralizedMultiset α := ⟦GenMulti.of_function f⟧
