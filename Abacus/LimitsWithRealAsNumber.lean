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


class ToFilter (α' α : Type*) where
  toFilter : α' → Filter α

class LimitOutput (β : Type*) where
  points : Type*
  toFilter : points → Filter β


def myTendsto {α α' β : Type*} [ToFilter α' α] [LimitOutput β]
  (f : α → β) (x₀ : α') (y₀ : LimitOutput.points β) : Prop :=
    Filter.Tendsto f (ToFilter.toFilter x₀) (LimitOutput.toFilter y₀)

def myLim {α α' β : Type*} [ToFilter α' α] [LimitOutput β]
  (f : α → β) (x₀ : α') : MaybeUndefined (LimitOutput.points β) :=
  MaybeUndefined.mk (myTendsto f x₀)

/- Instances for functions in the Reals, or Real-valued functions -/
instance ereal_to_filter_real : ToFilter EReal Real where
  toFilter
    | none           => Filter.atBot
    | some none      => Filter.atTop
    | some (some x') => nhds x'

instance (priority := high) : LimitOutput Real where
  points := EReal
  toFilter := ereal_to_filter_real.toFilter

/- Instances for metric spaces in general -/
instance {X : Type*} [MetricSpace X] : ToFilter X X := ⟨nhds⟩

instance {X : Type*} [MetricSpace X] : LimitOutput X := ⟨X, nhds⟩




/- Test type checking -/

/- Test for the functions `Real → Real` -/
#check myLim (fun x : Real => 1/x) (0 : Real)
#check myLim (fun x : Real => 1/x) (⊤ : EReal)
#check myLim (fun x : Real => 1/x) (0 : EReal)
#check_failure myLim (fun x : Real => 1/x) (0 : Nat)

#check myLim (fun x : Real => 1/x) (⊤ : EReal) = MaybeUndefined.of_defined (Real.toEReal 0)
#check myLim (fun x : Real => 1/x) (2 : Real)  = (Real.toEReal 0.5)


/- Test for functions to and from generic metric spaces -/
section test_metricspace

variable {Y : Type*} [MetricSpace Y] {a : Y}

#check myLim (fun y : Y => y) a
#check_failure myLim (fun y : Y => y) (0 : Real)
#check myLim (fun y : Y => y) a = MaybeUndefined.of_defined a
#check myLim (fun y : Y => dist y a) a = MaybeUndefined.of_defined (Real.toEReal 0)
#check myLim (fun y : Y => 1/(dist y a)) a = MaybeUndefined.of_defined (⊤ : EReal)

end test_metricspace
