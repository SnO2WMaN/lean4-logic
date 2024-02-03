 import Logic.Logic.LogicSymbol

namespace LO.Modal.Intuitionistic

@[notation_class] class FishArrow (α : Sort _) where
  fish_arrow : α → α → α

infixr:60 "⥽" => FishArrow.fish_arrow

class StrictImpModalLogicSymbol (α : Sort _) extends LogicSymbol α, FishArrow α

end LO.Modal.Intuitionistic
