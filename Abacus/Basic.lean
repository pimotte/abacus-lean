import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations


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


-- Code to make `|x|` notation possible for EReals
@[inherit_doc abs]
macro:max atomic("|" noWs) a:term noWs "|" : term => `(EReal.abs $a)

-- /-- Unexpander for the notation `|a|` for `abs a`.
-- Tries to add discretionary parentheses in unparsable cases. -/
-- @[app_unexpander abs]
-- meta def EReal.abs.unexpander : Lean.PrettyPrinter.Unexpander
--   | `($_ $a) =>
--     match a with
--     | `(|$_|) | `(|$_|ₘ) | `(-$_) => `(|($a)|)
--     | _ => `(|$a|)
--   | _ => throw ()


notation "Number" => EReal
-- Maybe make stucture or definition (how much unfolding is done automatically?)
notation "∞" => (⊤ : Number)
-- notation "-∞" => (⊥ : Number)   -- TODO: shoul be print only notation

variable (y : Number)
#check forall x : ℝ, x = y

def RealNumber : Set Number := {x | ∃ y : ℝ, x = y}
def NatNumber  : Set Number := {x | ∃ n : ℕ, x = n}

example {A : Set Number} (h : A ⊆ RealNumber) : Nonempty A := sorry
example : ∀ A ⊆ RealNumber, Nonempty A := sorry


def convergence_seq (a : Number → Number) (p : Number) : Prop :=
  ∀ ε ∈ RealNumber, ε > 0 → ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → |a n - p| < ε

example :  (∞ : EReal) - ∞  = -∞ := rfl
example : |(∞ : EReal) - ∞| =  ∞ := rfl
example : (-∞ : EReal) + ∞  = -∞ := rfl

def lim_seq (a : Number → Number) :=
  MaybeUndefined.mk (convergence_seq a)


theorem unique_convergence_seq {a : Number → Number} {p₁ p₂ : Number} (hp₁ : convergence_seq a p₁)
  (hp₂ : convergence_seq a p₂) : p₁ = p₂ := by
  by_contra
  -- lot of work, also because of ∞ and -∞
  -- maybe link to results from MathLib? Filter.Tendsto g b (nhds a))
  #check Topology.Hausdorff.tendsto_nhds_unique
  sorry

theorem lim_seq_iff_convergent_seq (a : Number → Number) (p : Number) :
  (lim_seq a = p) ↔ (convergence_seq a p) := by
  constructor
  · apply MaybeUndefined.satisfies_of_eq_defined
  · intro hp
    apply MaybeUndefined.eq_defined_of_unique_satisfies_of_satisfies hp
    exact unique_convergence_seq
