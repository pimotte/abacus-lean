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
def RealNumber : Set Number := {x | ∃ r : ℝ, x = r}
def RatNumber  : Set Number := {x | ∃ q : ℚ, x = q}
def IntNumber  : Set Number := {x | ∃ z : ℤ, x = z}
def NatNumber  : Set Number := {x | ∃ n : ℕ, x = n}



class LimitInput (α' α : Type*) where
  toFilter : α' → Filter α

class LimitOutput (β : Type*) where
  points : Type*
  toFilter : points → Filter β


open Topology

/- Instances for functions in the Reals, or Real-valued functions -/
instance ereal_to_filter_real : LimitInput EReal Real where
  toFilter
    | none           => Filter.atBot
    | some none      => Filter.atTop
    | some (some x') => 𝓝[≠] x'

instance (priority := high) : LimitOutput Real where
  points := EReal
  toFilter
    | none           => Filter.atBot
    | some none      => Filter.atTop
    | some (some x') => 𝓝 x'


/- Instances for topological spaces in general -/
instance {X : Type*} [TopologicalSpace X] : LimitInput X X := ⟨fun x => 𝓝[≠] x⟩

instance {X : Type*} [TopologicalSpace X] : LimitOutput X := ⟨X, 𝓝⟩




namespace LimitNoDomain

def myTendsto {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
  (f : α → β) (x₀ : α') (y₀ : LimitOutput.points β) : Prop :=
    Filter.Tendsto f (LimitInput.toFilter x₀) (LimitOutput.toFilter y₀)

def myLim {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
  (f : α → β) (x₀ : α') : MaybeUndefined (LimitOutput.points β) :=
  MaybeUndefined.mk (myTendsto f x₀)

/- Test for the functions `Real → Real` -/
#check myLim (fun x : Real => 1/x) (0 : Real)
#check myLim (fun x : Real => 1/x) (⊤ : EReal)
#check myLim (fun x : Real => 1/x) (0 : EReal)
#check_failure myLim (fun x : Real => 1/x) (0 : Nat)

#check myLim (fun x : Real => 1/x) (⊤ : EReal) = MaybeUndefined.of_defined (Real.toEReal 0)
#check myLim (fun x : Real => 1/x) (2 : Real)  = (Real.toEReal 0.5)


/- Test for functions to and from generic metric spaces -/
variable {Y : Type*} [MetricSpace Y] {a : Y}

#check myLim (fun y : Y => y) a
#check_failure myLim (fun y : Y => y) (0 : Real)
#check myLim (fun y : Y => y) a = MaybeUndefined.of_defined a
#check myLim (fun y : Y => dist y a) a = MaybeUndefined.of_defined (Real.toEReal 0)
#check myLim (fun y : Y => 1/(dist y a)) a = MaybeUndefined.of_defined (⊤ : EReal)

end LimitNoDomain



namespace Limit

def myTendsto {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
  (f : α → β) (D : Set α) (x₀ : α') (y₀ : LimitOutput.points β) : Prop :=
    Filter.Tendsto f (LimitInput.toFilter x₀ ⊓ Filter.principal D) (LimitOutput.toFilter y₀)

def myLim {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
  (f : α → β) (D : Set α) (x₀ : α') : MaybeUndefined (LimitOutput.points β) :=
  MaybeUndefined.mk (myTendsto f D x₀)

/- Test for the functions `Real → Real` -/
#check myLim (fun x : Real => 1/x) RealNumber (0 : Real)
#check myLim (fun x : Real => 1/x) NatNumber (⊤ : EReal)

#check myLim (fun x : Real => 1/x) RealNumber (⊤ : EReal) = (Real.toEReal 0)
#check myLim (fun x : Real => 1/x) NatNumber (2 : Real) = (Real.toEReal 0.5)


def tendsto_seq {β : Type*} [LimitOutput β] (a : Number → β) (y₀ : LimitOutput.points β) : Prop :=
  myTendsto a NatNumber (⊤ : EReal) y₀

def lim_seq {β : Type*} [LimitOutput β] (a : Number → β) :
  MaybeUndefined (LimitOutput.points β) := MaybeUndefined.mk (tendsto_seq a)



/- Rewrite `myTendsTo` and `tendsto_seq` to **all the** familiar definitions from analysis
for metric spaces -/

open Filter


/- Definitions for general convergence of functions, i.e. `myTendsTo`-/

/- Input `x → x₀` -/

lemma tendsto_pt_pt_def {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {f : X → Y} {D : Set X} {x₀ : X} {y₀ : Y} :
  myTendsto f D x₀ y₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε
  := sorry

lemma tendsto_pt_nr_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} {y₀ : Number} :
  myTendsto f D x₀ y₀.toEReal ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε
  := sorry

lemma tendsto_pt_infty_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} :
  myTendsto f D x₀ (⊤ : EReal) ↔
    ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x > M
  := sorry

lemma tendsto_pt_neginfty_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} :
  myTendsto f D x₀ (⊥ : EReal) ↔
    ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x < M
  := sorry

/- Input `x → ∞` -/

lemma tendsto_infty_pt_def {Y : Type*} [MetricSpace Y] {f : Number → Y} {D : Set Number} {y₀ : Y} :
  myTendsto f D (⊤ : EReal) y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε :=
  by
  have h_tendsto : myTendsto f D (⊤ : EReal) y₀ ↔ Tendsto f (atTop ⊓ 𝓟 D) (nhds y₀) := by rfl
  rw [h_tendsto]
  rw [Metric.tendsto_nhds]
  simp only [Filter.eventually_iff]
  constructor <;> intro h ε εpos
  · simp only [Filter.mem_inf_iff] at h
    obtain ⟨u, hu, s, hs, heq⟩ := h ε εpos
    simp only [mem_atTop_sets] at hu
    obtain ⟨z, hz⟩ := hu
    simp [Set.ext_iff] at heq; simp only [heq]
    use z
    exact (fun x xinD xgtz => ⟨hz x (le_of_lt xgtz), hs xinD⟩)
  · obtain ⟨z, hz⟩ := h ε εpos
    apply @Filter.monotone_mem _ _ ({x | x ≥ z + 1} ∩ D)
    · rintro x ⟨xgtzplus, xinD⟩
      refine hz x xinD (lt_of_lt_of_le ?_ xgtzplus)
      norm_num
    apply Filter.inter_mem_inf
    · apply mem_atTop
    · apply Filter.mem_principal_self

lemma tendsto_infty_nr_def {f : Number → Number} {D : Set Number} {y₀ : Number} :
  myTendsto f D (⊤ : EReal) y₀.toEReal ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε
  := sorry

lemma tendsto_infty_infty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D (⊤ : EReal) (⊤ : EReal) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x > z → f x > M
  := sorry

lemma tendsto_infty_neginfty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D (⊤ : EReal) (⊥ : EReal) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x > z → f x < M
  := sorry

/- input `x → -∞`-/

lemma tendsto_neginfty_pt_def {Y : Type*} [MetricSpace Y] {f : Number → Y} {D : Set Number} {y₀ : Y} :
  myTendsto f D (⊥ : EReal) y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x < z → dist (f x) y₀ < ε
  := sorry

lemma tendsto_neginfty_nr_def {f : Number → Number} {D : Set Number} {y₀ : Number} :
  myTendsto f D (⊥ : EReal) y₀.toEReal ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x < z → dist (f x) y₀ < ε
  := sorry

lemma tendsto_neginfty_infty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D (⊥ : EReal) (⊤ : EReal) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x < z → f x > M
  := sorry

lemma tendsto_neginfty_neginfty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D (⊥ : EReal) (⊥ : EReal) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x < z → f x < M
  := sorry



/- Translation into definitions for convergence of sequences -/

lemma tendsto_seq_pt_def {X : Type*} [MetricSpace X] {a : Number → X} {p : X} :
  tendsto_seq a p ↔
    ∀ ε > 0, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → dist (a n) p < ε :=
  by
  unfold tendsto_seq
  rw [tendsto_infty_pt_def]
  constructor <;> intro h ε εpos
  · obtain ⟨z, hz⟩ := h ε εpos
    obtain ⟨N, zgtN⟩ := exists_nat_gt z
    use N, ⟨N, rfl⟩
    intro n nnat ngeN
    apply hz n nnat
    exact lt_of_lt_of_le zgtN ngeN
  · obtain ⟨N, Nnat, hN⟩ := h ε εpos
    use N
    intro n nnat ngtN
    exact hN n nnat (le_of_lt ngtN)




/- At most one limit point -/

def AccPts {X : Type u_1} [TopologicalSpace X] (D : Set X) : Set X := {x | AccPt x (𝓟 D)}

/- Output in metric space -/

lemma myTendsto_pt_pt_unique {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
  {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {a b : Y}
  (ha : myTendsto f D x₀ a) (hb : myTendsto f D x₀ b) : a = b :=
  by
  #check tendsto_nhds_unique'
  sorry

lemma myTendsto_infty_pt_unique {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddAbove D) {a b : Y}
  (ha : myTendsto f D (⊤ : EReal) a) (hb : myTendsto f D (⊤ : EReal) b) : a = b :=
  by
  apply tendsto_nhds_unique' _ ha hb
  simp only [LimitInput.toFilter]
  rw [inf_principal_neBot_iff]
  intro U hU
  simp only [mem_atTop_sets] at hU
  obtain ⟨z, hz⟩ := hU
  rw [not_bddAbove_iff] at hD
  obtain ⟨x, xinD, zltx⟩ := hD z
  use x, hz _ (le_of_lt zltx)

lemma myTendsto_neginf_pt_unique {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddBelow D) {a b : Y}
  (ha : myTendsto f D (⊥ : EReal) a) (hb : myTendsto f D (⊥ : EReal) b) : a = b :=
  by
  #check tendsto_nhds_unique'
  sorry

/- Output in `Number` -/

lemma myTendsto_pt_nr_unique {X : Type*} [MetricSpace X] {f : X → Number}
  {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {a' b' : EReal}
  (ha' : myTendsto f D x₀ a') (hb' : myTendsto f D x₀ b') : a' = b' :=
  by
  sorry

lemma myTendsto_infty_nr_unique {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D)
  {a' b' : EReal} (ha' : myTendsto f D (⊤ : EReal) a') (hb' : myTendsto f D (⊤ : EReal) b') :
    a' = b' :=
  by
  sorry

lemma myTendsto_neginfty_nr_unique {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D)
  {a' b' : EReal} (ha' : myTendsto f D (⊥ : EReal) a') (hb' : myTendsto f D (⊥ : EReal) b') :
    a' = b' :=
  by
  sorry




end Limit
