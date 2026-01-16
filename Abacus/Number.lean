import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic
import Mathlib.Data.EReal.Operations

notation "Number" => Real
def RealNumber : Set Number := {x | ∃ r : Real, x = r}
def RatNumber  : Set Number := {x | ∃ q : Rat,  x = q}
def IntNumber  : Set Number := {x | ∃ z : Int,  x = z}
def NatNumber  : Set Number := {x | ∃ n : Nat,  x = n}

-- notation (priority := high) "ℝ" => RealNumber   -- `(priority := high)` from Yalep
-- notation (priority := high) "ℚ" => RatNumber
-- notation (priority := high) "ℤ" => IntNumber
-- notation (priority := high) "ℕ" => NatNumber

example (n : Number) := n ∈ NatNumber

/- Notation for infinities when they pop up. -/
notation "[-∞,∞]" => WithBot (WithTop Number)

notation "∞" => Top.top
notation "-∞" => Bot.bot

#check ∞
#check -∞




/- Coercions (code mainly taken from Yalep) -/

-- difficulté : les 0,1 et les suivants empruntent un chemin différent.
-- Si on caste tout le monde avec ofNat := (n:Number) (Real.instNatCast.natCast n)
-- on a ensuite les tactiques  (linarith, ring_nf etc ) qui ne fonctionnent plus ...

-- difficulty: 0,1 and subsequent take a different path.
-- If we cast everyone with ofNat := (n:Number) (Real.instNatCast.natCast n)
-- then we have the tactics (linarith, ring_nf etc) that don't work anymore...

@[default_instance 199]
instance instOfNatNumber {n : Nat} [n.AtLeastTwo] : OfNat Number n where
  ofNat := Real.instNatCast.natCast n

@[default_instance 200]
instance instOfNatNumber0 : OfNat Number 0 where
  ofNat := Real.instZero.zero

@[default_instance 200]
instance instOfNatNumber1 : OfNat Number 1 where
  ofNat := Real.instOne.one

-- note that these are provably the same
example : Real.instNatCast.natCast 0 = Real.instZero.zero := Nat.cast_zero
example : Real.instNatCast.natCast 1 = Real.instOne.one   := Nat.cast_one

#check 1
#check 2
#check 1/2

@[default_instance 501]
instance : OfScientific Number := by infer_instance

#check 0.5
