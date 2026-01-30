import Mathlib.Order.WithBot
import Abacus.MaybeUndefined

def extend_conservative {α β : Type*} (f : α → β) (U : MaybeUndefined (WithBot (WithTop α))) :
  MaybeUndefined (WithBot (WithTop β)) := Set.image (some ∘ some ∘ f) (Set.preimage (some ∘ some) U)
  -- remove all potential occurences of `⊥` and `⊤` in subset of `WithBotTop α`
  -- before mapping to `WithBotTop β` via `f`
  -- In effect, make effect of `f` on `⊥` and `⊤` undefined (empty set).

def extend_conservative2 {α β γ : Type*} (f : α → β → γ) (U : MaybeUndefined (WithBot (WithTop α)))
  (V : MaybeUndefined (WithBot (WithTop β))) : MaybeUndefined (WithBot (WithTop γ)) :=
  Set.image2 (fun (x : α) (y : β) ↦ some (some (f x y)))
    (Set.preimage (some ∘ some) U) (Set.preimage (some ∘ some) V)



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
