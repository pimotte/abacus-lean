import Mathlib.Data.Real.Basic
import Abacus.WithBotTopStructure

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
instance Number.instOfNat {n : Nat} [n.AtLeastTwo] : OfNat Number n where
  ofNat := Real.instNatCast.natCast n

@[default_instance 200]
instance Number.instOfNat0 : OfNat Number 0 where
  ofNat := Real.instZero.zero

@[default_instance 200]
instance Number.instOfNat1 : OfNat Number 1 where
  ofNat := Real.instOne.one

-- note that these are provably the same
example : Real.instNatCast.natCast 0 = Real.instZero.zero := Nat.cast_zero
example : Real.instNatCast.natCast 1 = Real.instOne.one   := Nat.cast_one

#check 1
#check 2
#check 1/2

@[default_instance 501]
instance Number.instOfScientific : OfScientific Number := by infer_instance

#check 0.5


/- Similarly, provide coercions for `MaybeUndefined [-∞,∞]` -/

-- Probably it suffices to give a single instance for `ofNat _ n`
-- (so no distinction for `n = 0` or `n = 1`)
-- since we do not expect to call `linarith` or `ring_nf` on terms of this type
--
-- Yet, implement same way as for `Number` so as to have definitional equality

instance WithBotTop.instOfNat {n : Nat} [n.AtLeastTwo] : OfNat (MaybeUndefined [-∞,∞]) n where
  ofNat := MaybeUndefined.of_def <| some <| some <| (@Number.instOfNat n _).ofNat

instance WithBotTop.instOfNat0 : OfNat (MaybeUndefined [-∞,∞]) 0 where
  ofNat := MaybeUndefined.of_def <| some <| some <| Number.instOfNat0.ofNat

instance WithBotTop.instOfNat1 : OfNat (MaybeUndefined [-∞,∞]) 1 where
  ofNat := MaybeUndefined.of_def <| some <| some <| Number.instOfNat1.ofNat

#check 1
#check (1 : MaybeUndefined [-∞,∞])

instance WithBotTop.instOfScientific : OfScientific (MaybeUndefined [-∞,∞]) where
  ofScientific mant expSgn decExp := MaybeUndefined.of_def <| some <| some <|
    Number.instOfScientific.ofScientific mant expSgn decExp

#check 0.5
#check (0.5 : MaybeUndefined [-∞,∞])
