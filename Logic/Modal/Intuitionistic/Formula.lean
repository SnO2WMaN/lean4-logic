import Logic.Modal.Intuitionistic.LogicSymbol

namespace LO.Modal.Intuitionistic

inductive Formula (α : Type u) : Type u where
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  | strimp : Formula α → Formula α → Formula α

namespace Formula

variable {α : Type u}

@[simp] def neg (p : Formula α) : Formula α := imp p falsum

@[simp] def verum : Formula α := neg falsum

instance : StrictImpModalLogicSymbol (Formula α) where
  tilde := neg
  arrow := imp
  wedge := and
  vee := or
  top := verum
  bot := falsum
  fish_arrow := strimp

instance : NegDefinition (Formula α) where
  neg := rfl

end Formula

end LO.Modal.Intuitionistic
