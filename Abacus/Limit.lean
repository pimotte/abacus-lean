import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Instances.Real.Lemmas


import Abacus.Number
import Abacus.MaybeUndefined




/- Define Limit concept -/

class LimitInput (α' α : Type*) where
  toFilter : α' → Filter α

class LimitOutput (β : Type*) where
  points : Type*
  toFilter : points → Filter β


open Topology

/- Instances for functions in the Reals, or Real-valued functions -/
instance : LimitInput EReal Real where
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

instance : Coe Number (LimitOutput.points Number) where
  coe := Real.toEReal

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
#check myLim (fun x : Real => 1/x) 0
#check myLim (fun x : Real => 1/x) ∞
#check myLim (fun x : Real => 1/x) 0
#check_failure myLim (fun x : Real => 1/x) (0 : Nat)

#check myLim (fun x : Real => 1/x) ∞ = (0 : Real)
#check myLim (fun x : Real => 1/x) (2 : Real) = (0.5 : Real)


/- Test for functions to and from generic metric spaces -/
variable {Y : Type*} [MetricSpace Y] {a : Y}

#check myLim (fun y : Y => y) a
#check_failure myLim (fun y : Y => y) (0 : Real)
#check myLim (fun y : Y => y) a = a
#check myLim (fun y : Y => dist y a) a = (0 : Real)
#check myLim (fun y : Y => 1/(dist y a)) a = ∞
#check myLim (fun y : Y => 1/(dist y a)) a = -∞

variable {b c : Number → Y} {p q : Y} [Add Y]
#check myLim (fun n => b n + c n) ∞ = p + q
#check myLim (fun n => b n + c n) ∞ = myLim b ∞ + myLim c ∞
#check myLim b ∞ + myLim c ∞ = p + q

example : (p + q : MaybeUndefined Y) = (p + q : Y) := by sorry
-- check `norm_cast`

variable {f g : Number → Number} {u v : Number}
#check myLim (fun x => f x + g x) (0 : Real) = u + v
#check_failure myLim (fun x => f x + g x) (0 : Real) = ∞ + v  -- as desired
-- don't want students to write this
-- If this would be desired, how to achieve this?

end LimitNoDomain



namespace Limit

def myTendsto {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
  (f : α → β) (D : Set α) (x₀ : α') (y₀ : LimitOutput.points β) : Prop :=
    Filter.Tendsto f (LimitInput.toFilter x₀ ⊓ Filter.principal D) (LimitOutput.toFilter y₀)

def myLim {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
  (f : α → β) (D : Set α) (x₀ : α') : MaybeUndefined (LimitOutput.points β) :=
  MaybeUndefined.mk (myTendsto f D x₀)

/- Test for the functions `Real → Real` -/
#check myLim (fun x : Real => 1/x) RealNumber 0
#check myLim (fun x : Real => 1/x) NatNumber ∞

#check myLim (fun x : Real => 1/x) RealNumber ∞ = (0 : Real)
#check myLim (fun x : Real => 1/x) NatNumber (2 : Real) = (0.5 : Real)
#check myLim (fun x : Real => 1/x) NatNumber (2 : Real) = -∞

def lim_seq {β : Type*} [LimitOutput β] (a : Number → β) :
  MaybeUndefined (LimitOutput.points β) := MaybeUndefined.mk (myTendsto a NatNumber ∞)



/- Rewrite `myTendsTo` and `tendsto_seq` to **all the** familiar definitions from analysis
for metric spaces -/

open Filter


/- Definitions for general convergence of functions, i.e. `myTendsTo`-/

/- Input `x → x₀` -/

lemma myTendsto_pt_pt_def {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {f : X → Y} {D : Set X} {x₀ : X} {y₀ : Y} :
  myTendsto f D x₀ y₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε
  := sorry

lemma myTendsto_pt_nr_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} {y₀ : Number} :
  myTendsto f D x₀ y₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε
  := sorry

lemma myTendsto_pt_infty_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} :
  myTendsto f D x₀ ∞ ↔
    ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x > M
  := sorry

lemma myTendsto_pt_neginfty_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} :
  myTendsto f D x₀ (-∞) ↔
    ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x < M
  := sorry

/- Input `x → ∞` -/

-- TODO: look for these equivalences in mathlib
lemma myTendsto_infty_pt_def {Y : Type*} [MetricSpace Y]
  {f : Number → Y} {D : Set Number} {y₀ : Y} :
  myTendsto f D ∞ y₀ ↔
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

lemma myTendsto_infty_nr_def {f : Number → Number} {D : Set Number} {y₀ : Number} :
  myTendsto f D ∞ y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε
  := sorry

lemma myTendsto_infty_infty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D ∞ ∞ ↔
    ∀ M, ∃ z, ∀ x ∈ D, x > z → f x > M
  := sorry

lemma myTendsto_infty_neginfty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D ∞ (-∞) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x > z → f x < M
  := sorry

/- input `x → -∞`-/

lemma myTendsto_neginfty_pt_def {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} {y₀ : Y} :
  myTendsto f D (-∞) y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x < z → dist (f x) y₀ < ε
  := sorry

lemma myTendsto_neginfty_nr_def {f : Number → Number} {D : Set Number} {y₀ : Number} :
  myTendsto f D (-∞) y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x < z → dist (f x) y₀ < ε
  := sorry

lemma myTendsto_neginfty_infty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D (-∞) ∞ ↔
    ∀ M, ∃ z, ∀ x ∈ D, x < z → f x > M
  := sorry

lemma myTendsto_neginfty_neginfty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D (-∞) (-∞) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x < z → f x < M
  := sorry



/- Translation into definitions for convergence of sequences -/

lemma tendsto_seq_pt_def {X : Type*} [MetricSpace X] {a : Number → X} {p : X} :
  myTendsto a NatNumber ∞ p ↔
    ∀ ε > 0, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → dist (a n) p < ε :=
  by
  rw [myTendsto_infty_pt_def]
  constructor <;> intro h ε εpos
  · obtain ⟨z, hz⟩ := h ε εpos
    obtain ⟨N, zltN⟩ := exists_nat_gt z
    use N, ⟨N, rfl⟩
    intro n nnat ngeN
    apply hz n nnat
    exact lt_of_lt_of_le zltN ngeN
  · obtain ⟨N, Nnat, hN⟩ := h ε εpos
    use N
    intro n nnat ngtN
    exact hN n nnat (le_of_lt ngtN)

lemma tendsto_seq_nr_def {a : Number → Number} {p : Number} :
  myTendsto a NatNumber ∞ p ↔
    ∀ ε > 0, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → dist (a n) p < ε := by
  sorry

lemma tendsto_seq_infty_def {a : Number → Number} :
  myTendsto a NatNumber ∞ ∞ ↔
    ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n > M := by
  sorry

lemma tendsto_seq_neginfty_def {a : Number → Number} :
  myTendsto a NatNumber ∞ (-∞) ↔
    ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n < M := by
  sorry




/- At most one limit point -/


/- Uniqueness of output for any non-trivial input filter -/

lemma myTendsto_metric_unique {α α' Y : Type*} [LimitInput α' α] [MetricSpace Y] {f : α → Y}
  {D : Set α} {x₀ : α'} (hIn : NeBot (LimitInput.toFilter x₀ ⊓ 𝓟 D)) {a b : Y}
  (ha : myTendsto f D x₀ a) (hb : myTendsto f D x₀ b) : a = b := tendsto_nhds_unique' hIn ha hb

lemma aux_unique_ereal (P : EReal → Prop) (notTopBot : ¬ (P ⊤ ∧ P ⊥))
  (notRealTop : ∀ x : Real, ¬ (P x ∧ P ⊤)) (notRealBot : ∀ x : Real, ¬ (P x ∧ P ⊥))
  (realUnique : ∀ x y : Real, P x → P y → x = y) :
  ∀ u v : EReal, P u → P v → u = v := by
  simp [EReal.forall]
  repeat
    and_intros
    tauto
    intro
  apply realUnique

lemma myTendsto_number_unique {α α' : Type*} [LimitInput α' α] {f : α → Number}
  {D : Set α} {x₀ : α'} (hIn : NeBot (LimitInput.toFilter x₀ ⊓ 𝓟 D)) {a b : EReal}
  (ha : myTendsto f D x₀ a) (hb : myTendsto f D x₀ b) : a = b := by
  apply aux_unique_ereal (myTendsto f D x₀) _ _ _ _ _ _ ha hb
  · show ¬(myTendsto f D x₀ (⊤ : EReal) ∧ myTendsto f D x₀ (⊥ : EReal))
    simp only [not_and]; intro hTop
    apply Tendsto.not_tendsto hTop
    simp only [LimitOutput.toFilter]
    apply Filter.disjoint_atTop_atBot
  · intro a'; simp only [not_and]; intro ha'
    apply not_tendsto_atTop_of_tendsto_nhds ha'
  · intro a'; simp only [not_and]; intro ha'
    apply not_tendsto_atBot_of_tendsto_nhds ha'
  · intro a' b' ha' hb'
    apply tendsto_nhds_unique ha' hb'


/- Conditions on domain `D` for which input filter is non-trivial -/

def AccPts {X : Type*} [TopologicalSpace X] (D : Set X) : Set X := {x | AccPt x (𝓟 D)}

lemma neBot_inputLimit_pt_iff_accPt {X : Type*} [MetricSpace X] {D : Set X} {x₀ : X} :
  x₀ ∈ AccPts D ↔ NeBot (LimitInput.toFilter x₀ ⊓ 𝓟 D) := by
  rfl

lemma neBot_inputLimit_infty_iff_notBddAbove {D : Set Number} :
  ¬BddAbove D ↔ NeBot (LimitInput.toFilter ∞ ⊓ 𝓟 D) := by
  simp only [LimitInput.toFilter]
  rw [inf_principal_neBot_iff]
  simp only [mem_atTop_sets]
  rw [not_bddAbove_iff]
  constructor <;> intro h
  · intro U hU
    obtain ⟨z, hz⟩ := hU
    obtain ⟨x, xinD, zltx⟩ := h z
    use x, hz _ (le_of_lt zltx)
  · intro x
    have hU : ∃ y, ∀ z ≥ y, z ∈ {z' | z' ≥ x + 1} := by
      use x + 1, fun _ h' => h'
    obtain ⟨y, ⟨hy, yinD⟩⟩ := h _ hU
    use y, yinD
    exact lt_of_lt_of_le (lt_add_one x) hy

lemma neBot_inputLimit_neginfty_iff_notBddBelow {D : Set Number} :
  ¬BddBelow D ↔ NeBot (LimitInput.toFilter (-∞) ⊓ 𝓟 D) := by
  simp only [EReal.neg_top]
  simp only [LimitInput.toFilter]
  rw [inf_principal_neBot_iff]
  simp only [mem_atBot_sets]
  rw [not_bddBelow_iff]
  constructor <;> intro h
  · intro U hU
    obtain ⟨z, hz⟩ := hU
    obtain ⟨x, xinD, zltx⟩ := h z
    use x, hz _ (le_of_lt zltx)
  · intro x
    have hU : ∃ y, ∀ z ≤ y, z ∈ {z' | z' + 1 ≤ x} := by
      use x - 1
      intro z zlexneg1
      simp; trans (x - 1 + 1)
      · rwa [add_le_add_iff_right]
      · rw [sub_add_cancel x]
    obtain ⟨y, ⟨hy, yinD⟩⟩ := h _ hU
    use y, yinD
    exact lt_of_lt_of_le (lt_add_one y) hy


/- Uniqueness of output given familiar conditions -/

/- Output in general metric space -/

lemma myTendsto_pt_pt_unique {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y}
  {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {a b : Y}
  (ha : myTendsto f D x₀ a) (hb : myTendsto f D x₀ b) : a = b := by
  apply myTendsto_metric_unique _ ha hb
  apply neBot_inputLimit_pt_iff_accPt.mp
  exact hx₀

lemma myTendsto_infty_pt_unique {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddAbove D) {a b : Y}
  (ha : myTendsto f D ∞ a) (hb : myTendsto f D ∞ b) : a = b := by
  apply myTendsto_metric_unique _ ha hb
  exact neBot_inputLimit_infty_iff_notBddAbove.mp hD

lemma myTendsto_neginfty_pt_unique {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddBelow D) {a b : Y}
  (ha : myTendsto f D (-∞) a) (hb : myTendsto f D (-∞) b) : a = b := by
  apply myTendsto_metric_unique _ ha hb
  exact neBot_inputLimit_neginfty_iff_notBddBelow.mp hD

/- Output in `Number` -/

lemma myTendsto_pt_nr_unique {X : Type*} [MetricSpace X] {f : X → Number}
  {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {a b : EReal}
  (ha : myTendsto f D x₀ a) (hb : myTendsto f D x₀ b) : a = b := by
  apply myTendsto_number_unique _ ha hb
  exact neBot_inputLimit_pt_iff_accPt.mp hx₀

lemma myTendsto_infty_nr_unique {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D)
  {a b : EReal} (ha : myTendsto f D ∞ a) (hb : myTendsto f D ∞ b) :
  a = b := by
  apply myTendsto_number_unique _ ha hb
  exact neBot_inputLimit_infty_iff_notBddAbove.mp hD

lemma myTendsto_neginfty_nr_unique {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D)
  {a b : EReal} (ha : myTendsto f D (-∞) a) (hb : myTendsto f D (-∞) b) :
  a = b := by
  apply myTendsto_number_unique _ ha hb
  exact neBot_inputLimit_neginfty_iff_notBddBelow.mp hD


/- Characterization of limits in terms of `myTendsto` -/

/- Functions -/

lemma myLim_pt_pt_def' {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {f : X → Y} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {y₀ : Y} :
  myLim f D x₀ = y₀ ↔ myTendsto f D x₀ y₀ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_pt_pt_unique hx₀

lemma myLim_pt_nr_def' {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {y₀ : Number} :
  myLim f D x₀ = y₀ ↔ myTendsto f D x₀ y₀ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_pt_nr_unique hx₀

lemma myLim_pt_infty_def' {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) :
  myLim f D x₀ = ∞ ↔ myTendsto f D x₀ ∞ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_pt_nr_unique hx₀

lemma myLim_pt_neginfty_def' {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) :
  myLim f D x₀ = (-∞ : EReal) ↔ -- TODO fix parsing of notation `-∞` as coercion to `EReal ??`
    myTendsto f D x₀ (-∞) := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_pt_nr_unique hx₀

/- Input `x → ∞` -/

lemma myLim_infty_pt_def' {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddAbove D) {y₀ : Y} :
  myLim f D ∞ = y₀ ↔ myTendsto f D ∞ y₀ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_pt_unique hD

lemma myLim_infty_nr_def' {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) {y₀ : Number} :
  myLim f D ∞ = y₀ ↔ myTendsto f D ∞ y₀ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_nr_unique hD

lemma myLim_infty_infty_def' {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) :
  myLim f D ∞ = ∞ ↔ myTendsto f D ∞ ∞ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_nr_unique hD

lemma myLim_infty_neginfty_def' {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) :
  myLim f D ∞ = (-∞ : EReal) ↔ myTendsto f D ∞ (-∞):= by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_nr_unique hD

/- input `x → -∞`-/

lemma myLim_neginfty_pt_def' {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddBelow D) {y₀ : Y} :
  myLim f D (-∞) = y₀ ↔ myTendsto f D (-∞) y₀ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_neginfty_pt_unique hD

lemma myLim_neginfty_nr_def' {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D)
  {y₀ : Number} : myLim f D (-∞) = y₀ ↔ myTendsto f D (-∞) y₀ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_neginfty_nr_unique hD

lemma myLim_neginfty_infty_def' {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D) :
  myLim f D (-∞) = ∞ ↔ myTendsto f D (-∞) ∞ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_neginfty_nr_unique hD

lemma myLim_neginfty_neginfty_def' {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D) :
  myLim f D (-∞) = (-∞ : EReal) ↔ myTendsto f D (-∞) (-∞) := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_neginfty_nr_unique hD


/- Characterization of limits of sequences -/

lemma notBddAbove_natNumber : ¬BddAbove NatNumber := by
  rw [not_bddAbove_iff]
  intro x
  obtain ⟨N, _⟩ := exists_nat_gt x
  use N, ⟨N, rfl⟩

lemma lim_seq_pt_def' {X : Type*} [MetricSpace X] {a : Number → X} {p : X} :
  lim_seq a = p ↔ myTendsto a NatNumber ∞ p := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_pt_unique notBddAbove_natNumber

lemma lim_seq_nr_def' {a : Number → Number} {p : Number} :
  lim_seq a = p ↔ myTendsto a NatNumber ∞ p := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_nr_unique notBddAbove_natNumber

lemma lim_seq_infty_def' {a : Number → Number} :
  lim_seq a = ∞ ↔ myTendsto a NatNumber ∞ ∞ := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_nr_unique notBddAbove_natNumber

lemma lim_seq_neginfty_def' {a : Number → Number} :
  lim_seq a = (-∞ : EReal) ↔ myTendsto a NatNumber ∞ (-∞) := by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_infty_nr_unique notBddAbove_natNumber


/- Characterization of limits in familiar terms -/

/- Functions -/

/- Input `x → x₀` -/

lemma myLim_pt_pt_def {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  {f : X → Y} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {y₀ : Y} :
  myLim f D x₀ = y₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε := by
  rw [myLim_pt_pt_def' hx₀, ← myTendsto_pt_pt_def]

lemma myLim_pt_nr_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) {y₀ : Number} :
  myLim f D x₀ = y₀ ↔
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε := by
  rw [myLim_pt_nr_def' hx₀, ← myTendsto_pt_nr_def]

lemma myLim_pt_infty_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) :
  myLim f D x₀ = ∞ ↔
    ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x > M := by
  rw [myLim_pt_infty_def' hx₀, ← myTendsto_pt_infty_def]

lemma myLim_pt_neginfty_def {X : Type*} [MetricSpace X]
  {f : X → Number} {D : Set X} {x₀ : X} (hx₀ : x₀ ∈ AccPts D) :
  myLim f D x₀ = (-∞ : EReal) ↔ -- TODO fix parsing of notation `-∞` as coercion to `EReal ??`
    ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x < M := by
  rw [myLim_pt_neginfty_def' hx₀, ← myTendsto_pt_neginfty_def]

/- Input `x → ∞` -/

lemma myLim_infty_pt_def {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddAbove D) {y₀ : Y} :
  myLim f D ∞ = y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε := by
  rw [myLim_infty_pt_def' hD, ← myTendsto_infty_pt_def]

lemma myLim_infty_nr_def {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) {y₀ : Number} :
  myLim f D ∞ = y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε := by
  rw [myLim_infty_nr_def' hD, ← myTendsto_infty_pt_def]
  rfl

lemma myLim_infty_infty_def {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) :
  myLim f D ∞ = ∞ ↔
    ∀ M, ∃ z, ∀ x ∈ D, x > z → f x > M := by
  rw [myLim_infty_infty_def' hD, ← myTendsto_infty_infty_def]

lemma myLim_infty_neginfty_def {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) :
  myLim f D ∞ = (-∞ : EReal) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x > z → f x < M := by
  rw [myLim_infty_neginfty_def' hD, ← myTendsto_infty_neginfty_def]

/- input `x → -∞`-/

lemma myLim_neginfty_pt_def {Y : Type*} [MetricSpace Y] {f : Number → Y}
  {D : Set Number} (hD : ¬BddBelow D) {y₀ : Y} :
  myLim f D (-∞) = y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x < z → dist (f x) y₀ < ε := by
  rw [myLim_neginfty_pt_def' hD, ← myTendsto_neginfty_pt_def]

lemma myLim_neginfty_nr_def {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D)
  {y₀ : Number} : myLim f D (-∞) = y₀ ↔
    ∀ ε > 0, ∃ z, ∀ x ∈ D, x < z → dist (f x) y₀ < ε := by
  rw [myLim_neginfty_nr_def' hD, ← myTendsto_neginfty_pt_def]
  rfl

lemma myLim_neginfty_infty_def {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D) :
  myLim f D (-∞) = ∞ ↔
    ∀ M, ∃ z, ∀ x ∈ D, x < z → f x > M := by
  rw [myLim_neginfty_infty_def' hD, ← myTendsto_neginfty_infty_def]

lemma myLim_neginfty_neginfty_def {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D) :
  myLim f D (-∞) = (-∞ : EReal) ↔
    ∀ M, ∃ z, ∀ x ∈ D, x < z → f x < M := by
  rw [myLim_neginfty_neginfty_def' hD, ← myTendsto_neginfty_neginfty_def]


/- Limits of equences -/

lemma lim_seq_pt_def {X : Type*} [MetricSpace X] {a : Number → X} {p : X} :
  lim_seq a = p ↔
    ∀ ε > 0, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → dist (a n) p < ε := by
  rw [lim_seq_pt_def', ← tendsto_seq_pt_def]

lemma lim_seq_nr_def {a : Number → Number} {p : Number} :
  lim_seq a = p ↔
    ∀ ε > 0, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → dist (a n) p < ε := by
  rw [lim_seq_nr_def', ← tendsto_seq_nr_def]

lemma lim_seq_infty_def {a : Number → Number} :
  lim_seq a = ∞ ↔
    ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n > M := by
  rw [lim_seq_infty_def', ← tendsto_seq_infty_def]

lemma lim_seq_neginfty_def {a : Number → Number} :
  lim_seq a = (-∞ : EReal) ↔
    ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n < M := by
  rw [lim_seq_neginfty_def', ← tendsto_seq_neginfty_def]


#check Option.map₂



end Limit
