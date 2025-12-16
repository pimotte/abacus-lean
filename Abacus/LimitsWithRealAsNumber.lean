import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Instances.Real.Lemmas

def MaybeUndefined (α : Type*) := Set α
/- `Set α` instead of `α → Prop` because this gives lots of nice infrastructure for free,
such as `Set.singleton` and `Set.map2` -/

-- notation
postfix:max "??" => MaybeUndefined

namespace MaybeUndefined

@[ext]
theorem ext {α : Type*} {P Q : MaybeUndefined α} (h : ∀ x : α, P x ↔ Q x) : P = Q :=
  funext (fun x ↦ propext (h x))

def mk {α : Type*} (P : α → Prop) : MaybeUndefined α := P
def of_defined {α : Type*} (x : α) : MaybeUndefined α := Set.singleton x

instance {α : Type*} : Coe α (MaybeUndefined α) where
  coe := of_defined


/- Establish key properties of `MaybeUndefined α`
(theorem names can be improved) -/

theorem satisfies_of_eq_defined {α : Type} {P : α → Prop} {x : α}
  (h : mk P = x) : P x := by
  unfold mk of_defined Set.singleton at h
  rw [h]
  rfl

theorem unique_satisfies_of_eq_defined {α : Type} {P : α → Prop} {x y : α}
  (h : mk P = x) (hy : P y) : y = x := by
  unfold mk of_defined Set.singleton at h
  rwa [h] at hy

theorem eq_defined_of_unique_satisfies_of_satisfies {α : Type} {P : α → Prop} {x : α}
  (hx : P x) (hunique : ∀ {y z}, P y → P z → y = z) : mk P = x := by
  ext y
  constructor <;> intro hy
  · exact hunique hy hx
  · rwa [hy]

end MaybeUndefined



notation "Number" => Real



class LimSpecsOut (β : Type*) where
  param : Type*
  toFilter : param → Filter β

class LimSpecsIn (α α' : Type*) where
  toFilter : α' → Filter α


def myTendsto {α α' β : Type*} [LimSpecsIn α α'] [LimSpecsOut β]
  (f : α → β) (x₀ : α') (y₀ : LimSpecsOut.param β) : Prop :=
    Filter.Tendsto f (LimSpecsIn.toFilter x₀) (LimSpecsOut.toFilter y₀)

def myLim {α α' β : Type*} [LimSpecsIn α α'] [LimSpecsOut β]
  (f : α → β) (x₀ : α') :=
  MaybeUndefined.mk (myTendsto f x₀)



instance : LimSpecsOut Real where
  param := EReal
  toFilter
    | none           => Filter.atBot
    | some none      => Filter.atTop
    | some (some x') => nhds x'

instance : LimSpecsIn Real EReal where
  toFilter
    | none           => Filter.atBot
    | some none      => Filter.atTop
    | some (some x') => nhds x'

instance : LimSpecsIn Real Real where
  toFilter := nhds


#check myLim (fun x : Real => 1/x) (0 : Real)
#check myLim (fun x : Real => 1/x) (⊤ : EReal)
#check myLim (fun x : Real => 1/x) (0 : EReal)
#check_failure myLim (fun x : Real => 1/x) (0 : Nat)


#check myLim (fun x : Real => 1/x) (⊤ : EReal) =
  MaybeUndefined.of_defined (Real.toEReal 0)
#check myLim (fun x : Real => 1/x) (2 : Real) =
  MaybeUndefined.of_defined (Real.toEReal 0.5)
