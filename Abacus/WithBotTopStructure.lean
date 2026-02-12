import Mathlib.Order.WithBot
import Abacus.MaybeUndefined
import Mathlib.Data.Real.Basic -- needed for correct functioning `to_additive`


/- Make effect of `f` on `⊥` and `⊤` undefined. -/
def extend_conservative {α β : Type*} (f : α → β) :
  MaybeUndefined (WithBot (WithTop α)) → MaybeUndefined (WithBot (WithTop β))
  | some (some (some x)) => some (some (some (f x)))
  | _ => none

/- Make effect of `f` on `⊥` and `⊤` undefined. -/
def extend_conservative2 {α β γ : Type*} (f : α → β → γ) : MaybeUndefined (WithBot (WithTop α)) →
  MaybeUndefined (WithBot (WithTop β)) → MaybeUndefined (WithBot (WithTop γ))
  | some (some (some x)), some (some (some y)) => some (some (some (f x y)))
  | _, _ => none

@[to_additive]
protected def WithBotTop.mul_conservative {α : Type*} [Mul α] :
  Mul (MaybeUndefined (WithBot (WithTop α))) :=
  ⟨extend_conservative2 Mul.mul⟩

attribute [instance] WithBotTop.mul_conservative WithBotTop.add_conservative

@[to_additive]
protected def WithBotTop.inv_conservative {α : Type*} [Inv α] :
  Inv (MaybeUndefined (WithBot (WithTop α))) :=
  ⟨extend_conservative Inv.inv⟩

attribute [instance] WithBotTop.inv_conservative WithBotTop.neg_conservative

@[to_additive]
protected def WithBotTop.div_conservative {α : Type*} [Div α] :
  Div (MaybeUndefined (WithBot (WithTop α))) :=
  ⟨extend_conservative2 Div.div⟩

attribute [instance] WithBotTop.div_conservative WithBotTop.sub_conservative
