import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.EReal.Operations



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


open EReal

notation "Number" => EReal
-- Maybe make stucture or definition (how much unfolding is done automatically?)

def MaybeUndefined (α : Type*) := (α → Prop)
postfix:max "??"  => MaybeUndefined

def MaybeUndefined.mk {α : Type*} (P : α → Prop) : MaybeUndefined α := P
def MaybeUndefined.defined {α : Type*} (x : α) : MaybeUndefined α := (fun y : α ↦ (y = x))

instance {α : Type*}: Coe α (MaybeUndefined α) where
  coe := MaybeUndefined.defined


variable (y : Number)
#check forall x : ℝ, x = y

def RealNumber : Set Number := {x | ∃ y : ℝ, x = y}
def NatNumber  : Set Number := {x | ∃ n : ℕ, x = n}

example {A : Set Number} (h : A ⊆ RealNumber) : Nonempty A := sorry
example : ∀ A ⊆ RealNumber, Nonempty A := sorry


def convergence_seq (a : Number → Number) (p : Number) : Prop :=
  ∀ ε ∈ RealNumber, ε > 0 → ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → |a n - p| < ε

#eval |(⊤ : EReal) - ⊤|
#eval |(⊥ : EReal) - ⊥|

def lim_seq (a : Number → Number) :=
  MaybeUndefined.mk (convergence_seq a)

example (a : Number → Number) (p : Number) : (lim_seq a = p) ↔ (convergence_seq a p) := by
  unfold lim_seq
  unfold MaybeUndefined.defined
  unfold MaybeUndefined.mk
  constructor <;> intro h
  · rw [h]
  · ext p' -- ext lemma maken en registreren
