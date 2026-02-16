import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Instances.Real.Lemmas

import Abacus.Number
import Abacus.MaybeUndefined
import Abacus.WithBotTopStructure


section DiscreteOrder   -- TODO: turn into module?
                        -- At least something that needs to be opened explicitly

/- Define a discrete order on metric spaces such that these can be used
with the new limit concept -/

instance (priority := low) discreteOrder (α : Type*) [MetricSpace α] : PartialOrder α where
  /- limit to `MetricSpace` to prevent spread of this trivial order by means of type inference -/
  le := Eq
  le_refl := Eq.refl
  le_trans := @Eq.trans α
  le_antisymm := fun a b p _ ↦ p

/- Interaction topology with a discrete order -/

instance {α : Type*} [MetricSpace α] [Nontrivial α] : @NoTopOrder α (discreteOrder α).toLE where
  exists_not_le (a : α) := by
    simp only [LE.le]
    rwa [← nontrivial_iff_exists_ne a]

instance {α : Type*} [MetricSpace α] [Nontrivial α] : @NoBotOrder α (discreteOrder α).toLE where
  exists_not_ge (a : α) := by
    simp only [LE.le]
    have : ∃ b, ¬b = a := by rwa [← nontrivial_iff_exists_ne a]
    obtain ⟨b, h⟩ := this
    exact ⟨b, fun heq ↦ h heq.symm⟩ -- should be a simpler way to transform `a ≠ b` into `b ≠ a`

instance {α : Type*} [MetricSpace α] : @ClosedIicTopology α _ (discreteOrder α).toPreorder where
  isClosed_Iic (a : α) := by apply isClosed_singleton

instance {α : Type*} [MetricSpace α] : @ClosedIciTopology α _ (discreteOrder α).toPreorder where
  isClosed_Ici (a : α) := by
    have : Set.Ici a = {a} := by
      ext b
      simp only [Set.mem_Ici, Set.mem_singleton_iff]
      rw [Eq.comm]; rfl
    rw [this]
    apply isClosed_singleton

end DiscreteOrder



namespace Limit

open Filter Topology

def input_filter {α : Type*} [TopologicalSpace α] [Preorder α]
  (D : Set α) (x₀ : WithBot (WithTop α)) : Filter α :=
  match x₀ with
  | none            => atBot ⊓ 𝓟 D
  | some none       => atTop ⊓ 𝓟 D
  | some (some x₀)  => nhdsWithin x₀ (D \ {x₀})

def output_filter {α : Type*} [TopologicalSpace α] [Preorder α]
  (y₀ : WithBot (WithTop α)) : Filter α :=
  match y₀ with
  | none            => atBot
  | some none       => atTop
  | some (some y₀)  => 𝓝 y₀

def myTendsto {α β : Type*} [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β]
  (f : α → β) (D : Set α) (x₀ : WithBot (WithTop α)) (y₀ : WithBot (WithTop β)) : Prop :=
  Filter.Tendsto f (input_filter D x₀) (output_filter y₀)

noncomputable def myLim {α β : Type*} [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β]
  (f : α → β) (D : Set α) (x₀ : WithBot (WithTop α)) : MaybeUndefined (WithBot (WithTop β)) :=
  MaybeUndefined.unique_satisfier (myTendsto f D x₀)

noncomputable def lim_seq {β : Type*} [TopologicalSpace β] [Preorder β] (seq : Number → β) :
  MaybeUndefined (WithBot (WithTop β)) := MaybeUndefined.unique_satisfier (myTendsto seq NatNumber ∞)


/- Test limit inputs -/

section Test

#check myLim (fun x : Number => 1/x) RealNumber 0
#check myLim (fun x : Real => 1/x) RealNumber 2 = (1/2 : Real)
#check myLim (fun x : Real => 1/x) RealNumber 0 = MaybeUndefined.of_def ∞
#check myLim (fun x : Real => 1/x) RealNumber 0 = MaybeUndefined.of_def -∞
#check myLim (fun x : Real => 1/x) RealNumber ∞ = MaybeUndefined.of_def 0
#check myLim (fun x : Real => 1/x) RealNumber -∞ = MaybeUndefined.of_def 0

variable {Y : Type*} [MetricSpace Y] {a : Y}

#check myLim (fun y : Y => y) Set.univ a
#check_failure myLim (fun y : Y => y) Set.univ 0
#check myLim (fun y : Y => y) Set.univ a = a
#check myLim (fun y : Y => y) Set.univ ∞ = a
#check myLim (fun y : Y => dist y a) Set.univ a = MaybeUndefined.of_def 0
#check myLim (fun y : Y => 1/(dist y a)) Set.univ a = MaybeUndefined.of_def ∞
#check myLim (fun y : Y => 1/(dist y a)) Set.univ a = MaybeUndefined.of_def -∞

end Test




-- namespace LimitNoDomain

-- def myTendsto {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
--   (f : α → β) (x₀ : α') (y₀ : LimitOutput.points β) : Prop :=
--     Filter.Tendsto f (LimitInput.toFilter x₀) (LimitOutput.toFilter y₀)

-- def myLim {α α' β : Type*} [LimitInput α' α] [LimitOutput β]
--   (f : α → β) (x₀ : α') : MaybeUndefined (LimitOutput.points β) :=
--   MaybeUndefined.mk (myTendsto f x₀)

-- /- Test for the functions `Real → Real` -/
-- #check myLim (fun x : Real => 1/x) 0
-- #check myLim (fun x : Real => 1/x) ∞
-- #check myLim (fun x : Real => 1/x) 0
-- #check_failure myLim (fun x : Real => 1/x) (0 : Nat)

-- #check myLim (fun x : Real => 1/x) ∞ = 0
-- #check myLim (fun x : Real => 1/x) (2 : Real) = (0.5 : Real)


-- /- Test for functions to and from generic metric spaces -/
-- variable {Y : Type*} [MetricSpace Y] {a : Y}

-- #check myLim (fun y : Y => y) a
-- #check_failure myLim (fun y : Y => y) (0 : Real)
-- #check myLim (fun y : Y => y) a = a
-- #check myLim (fun y : Y => dist y a) a = (0 : Real)
-- #check myLim (fun y : Y => 1/(dist y a)) a = ∞
-- #check myLim (fun y : Y => 1/(dist y a)) a = -∞

-- variable {b c : Number → Y} {p q : Y} [Add Y]
-- #check myLim (fun n => b n + c n) ∞ = p + q
-- #check myLim (fun n => b n + c n) ∞ = myLim b ∞ + myLim c ∞
-- #check myLim b ∞ + myLim c ∞ = p + q

-- example : (p + q : MaybeUndefined Y) = (p + q : Y) := by sorry
-- -- check `norm_cast`

-- variable {f g : Number → Number} {u v : Number}
-- #check myLim (fun x => f x + g x) (0 : Real) = u + v
-- #check_failure myLim (fun x => f x + g x) (0 : Real) = ∞ + v  -- as desired
-- -- don't want students to write this
-- -- If this would be desired, how to achieve this?

-- end LimitNoDomain


section Uniqueness

/- At most one limit point -/

/- Uniqueness of output for any non-trivial input filter -/

lemma aux_unique_withbottop {α : Type*} (P : WithBot (WithTop α) → Prop) (notTopBot : ¬ (P ⊤ ∧ P ⊥))
  (notValTop : ∀ x : α, ¬ (P x ∧ P ⊤)) (notValBot : ∀ x : α, ¬ (P x ∧ P ⊥))
  (valUnique : ∀ x y : α, P x → P y → x = y) :
  ∀ u v : WithBot (WithTop α), P u → P v → u = v :=
  by
  simp [WithBot.forall, WithTop.forall]
  repeat
    and_intros
    tauto
    intro
  apply valUnique

lemma myTendsto_unique {α β : Type*} [TopologicalSpace α] [Preorder α]
  [TopologicalSpace β] [T2Space β] [Nontrivial β] [PartialOrder β] [NoTopOrder β] [NoBotOrder β]
  [ClosedIciTopology β] [ClosedIicTopology β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} (hIn : NeBot (input_filter D x₀))
  {y₁ y₂ : WithBot (WithTop β)} (h₁ : myTendsto f D x₀ y₁) (h₂ : myTendsto f D x₀ y₂) : y₁ = y₂ :=
  by
  apply aux_unique_withbottop (myTendsto f D x₀) _ _ _ _ _ _ h₁ h₂
  · /- Cannot go to both `∞` and `-∞` -/
    simp only [not_and]; intro h_infty
    apply Tendsto.not_tendsto h_infty
    simp only [output_filter]
    apply Filter.disjoint_atTop_atBot
  · /- Cannot go to both `y : β` and `∞` -/
    intro y; simp only [not_and]; intro h
    apply not_tendsto_atTop_of_tendsto_nhds h
  · /- Cannot go to both `y : β` and `-∞` -/
    intro y; simp only [not_and]; intro h
    apply not_tendsto_atBot_of_tendsto_nhds h
  · /- Cannot go to two values `y₁ : β` and `y₂ : β` at once -/
    intro y₁ y₂ h₁ h₂
    apply tendsto_nhds_unique h₁ h₂


/- Conditions on domain `D` for which input filter is non-trivial -/

def AccPts {X : Type*} [TopologicalSpace X] (D : Set X) : Set X := {x | AccPt x (𝓟 D)}

lemma neBot_inputFilter_pt_iff_accPt {X : Type*} [TopologicalSpace X] [Preorder X]
  {D : Set X} {x₀ : X} :
  NeBot (input_filter D x₀)  ↔  x₀ ∈ AccPts D := by
    simp [input_filter, AccPts, AccPts, accPt_principal_iff_nhdsWithin]

lemma neBot_inputFilter_infty_iff_notBddAbove {D : Set Number} :
  NeBot (input_filter D ∞) ↔ ¬BddAbove D := by
  simp only [input_filter]
  rw [inf_principal_neBot_iff]
  simp only [mem_atTop_sets]
  rw [not_bddAbove_iff]
  constructor <;> intro h
  · intro x
    have hU : ∃ y, ∀ z ≥ y, z ∈ {z' | z' ≥ x + 1} := by
      use x + 1, fun _ h' => h'
    obtain ⟨y, ⟨hy, yinD⟩⟩ := h _ hU
    use y, yinD
    exact lt_of_lt_of_le (lt_add_one x) hy
  · intro U hU
    obtain ⟨z, hz⟩ := hU
    obtain ⟨x, xinD, zltx⟩ := h z
    use x, hz _ (le_of_lt zltx)

lemma neBot_inputFilter_neginfty_iff_notBddBelow {D : Set Number} :
  NeBot (input_filter D -∞) ↔ ¬BddBelow D := by
  simp only [input_filter]
  rw [inf_principal_neBot_iff]
  simp only [mem_atBot_sets]
  rw [not_bddBelow_iff]
  constructor <;> intro h
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
  · intro U hU
    obtain ⟨z, hz⟩ := hU
    obtain ⟨x, xinD, zltx⟩ := h z
    use x, hz _ (le_of_lt zltx)

end Uniqueness



section Characterizations

/- Characterizations of `myTendsto` into familiar definition -/
-- TODO: look for these equivalences in mathlib

/- Input `x → x₀` -/

lemma myTendsto_pt_pt_def {α β : Type*} [MetricSpace α] [Preorder α] [MetricSpace β] [Preorder β]
  {f : α → β} {D : Set α} {x₀ : α} {y₀ : β} :
  myTendsto f D x₀ y₀
    ↔  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε :=
  by
  unfold myTendsto input_filter output_filter
  simp only [gt_iff_lt, dist_pos, ne_eq, and_imp]
  rw [Metric.tendsto_nhdsWithin_nhds]
  grind

lemma myTendsto_pt_infty_def {α : Type*} [MetricSpace α] [Preorder α]
  {f : α → Number} {D : Set α} {x₀ : α} :
  myTendsto f D x₀ ∞
    ↔  ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x ≥ M := by
  unfold myTendsto input_filter output_filter
  simp only [gt_iff_lt, dist_pos, ne_eq, and_imp]
  rw [Metric.nhdsWithin_basis_ball.tendsto_iff atTop_basis]
  simp only [Set.mem_inter_iff, Metric.mem_ball, Set.mem_diff, Set.mem_singleton_iff, Set.mem_Ici,
    and_imp, forall_const, ge_iff_le]
  refine forall_congr' fun M ↦ ?_
  grind

lemma myTendsto_pt_neginfty_def {α : Type*} [MetricSpace α] [Preorder α]
  {f : α → Number} {D : Set α} {x₀ : α} :
  myTendsto f D x₀ -∞
    ↔  ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x ≤ M :=
  by
  unfold myTendsto input_filter output_filter
  simp only [gt_iff_lt, dist_pos, ne_eq, and_imp]
  rw [Metric.nhdsWithin_basis_ball.tendsto_iff atBot_basis]
  simp only [Set.mem_inter_iff, Metric.mem_ball, Set.mem_diff, Set.mem_singleton_iff, Set.mem_Iic,
    and_imp, forall_const]
  refine forall_congr' ?_
  grind

/- Input `x → ∞` -/

lemma myTendsto_infty_pt_def {β : Type*} [MetricSpace β] [Preorder β]
  {f : Number → β} {D : Set Number} {y₀ : β} :
  myTendsto f D ∞ y₀  ↔  ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε :=
  by
  simp only [myTendsto, input_filter, output_filter]
  rw [Metric.tendsto_nhds]
  simp only [Filter.eventually_iff]
  constructor <;> intro h ε εpos
  · simp only [Filter.mem_inf_iff] at h
    obtain ⟨u, hu, s, hs, heq⟩ := h ε εpos
    rw [mem_atTop_sets] at hu
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

lemma myTendsto_infty_infty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D ∞ ∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≥ z → f x ≥ M :=
  by
  unfold myTendsto input_filter output_filter
  rw [(atTop_basis.inf_principal _).tendsto_iff atTop_basis]
  simp only [Set.mem_inter_iff, Set.mem_Ici, and_imp, true_and, forall_const, ge_iff_le]
  refine forall_congr' fun M ↦ ?_
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h
    use x
    grind
  · obtain ⟨x, hx⟩ := h
    use x
    grind

lemma myTendsto_infty_neginfty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D ∞ -∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≥ z → f x ≤ M :=
  by
  unfold myTendsto input_filter output_filter
  rw [(atTop_basis.inf_principal _).tendsto_iff atBot_basis]
  simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, and_imp, true_and, forall_const]
  refine forall_congr' fun M ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h
    use x
    grind
  · obtain ⟨x, hx⟩ := h
    use x
    grind

/- Input `x → -∞` -/

lemma myTendsto_neginfty_pt_def {β : Type*} [MetricSpace β] [Preorder β]
  {f : Number → β} {D : Set Number} {y₀ : β} :
  myTendsto f D -∞ y₀  ↔  ∀ ε > 0, ∃ z, ∀ x ∈ D, x ≤ z → dist (f x) y₀ < ε :=
  by
  unfold myTendsto input_filter output_filter
  simp only [gt_iff_lt]
  rw [(atBot_basis.inf_principal _).tendsto_iff Metric.nhds_basis_ball]
  simp only [Set.mem_inter_iff, Set.mem_Iic, Metric.mem_ball, and_imp, true_and]
  refine forall_congr' fun M ↦ ⟨fun h hM ↦ ?_, fun h hM ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h hM
    use x
    grind
  · obtain ⟨x, hx⟩ := h hM
    use x
    grind

lemma myTendsto_neginfty_infty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D -∞ ∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≤ z → f x ≥ M :=
  by
  unfold myTendsto input_filter output_filter
  rw [(atBot_basis.inf_principal _).tendsto_iff atTop_basis]
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ici, and_imp, true_and, forall_const]
  refine forall_congr' fun M ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h
    use x
    grind
  · obtain ⟨x, hx⟩ := h
    use x
    grind

lemma myTendsto_neginfty_neginfty_def {f : Number → Number} {D : Set Number} :
  myTendsto f D -∞ -∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≤ z → f x ≤ M :=
  by
  unfold myTendsto input_filter output_filter
  rw [(atBot_basis.inf_principal _).tendsto_iff atBot_basis]
  simp only [Set.mem_inter_iff, Set.mem_Iic, and_imp, true_and, forall_const]
  refine forall_congr' fun M ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨x, hx⟩ := h
    use x
    grind
  · obtain ⟨x, hx⟩ := h
    use x
    grind

/- Characterization of `myTendsto` for sequences into familiar terms -/

lemma myTendsto_seq_pt_def {β : Type*} [MetricSpace β] [Preorder β]
  {a : Number → β} {p : β} :
  myTendsto a NatNumber ∞ p  ↔
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

lemma myTendsto_seq_infty_def {a : Number → Number} :
  myTendsto a NatNumber ∞ ∞  ↔  ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n > M :=
  by
  sorry

lemma myTendsto_seq_neginfty_def {a : Number → Number} :
  myTendsto a NatNumber ∞ -∞  ↔  ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n < M :=
  by
  sorry


/- Characterization of `myLim` in terms of `myTendsto` (for unique limits) -/

lemma myLim_iff_myTendsto {α β : Type*} [TopologicalSpace α] [Preorder α]
  [TopologicalSpace β] [T2Space β] [Nontrivial β] [PartialOrder β] [NoTopOrder β] [NoBotOrder β]
  [ClosedIciTopology β] [ClosedIicTopology β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} (hIn : NeBot (input_filter D x₀))
  {y₀ : WithBot (WithTop β)} :
    myLim f D x₀ = y₀  ↔  myTendsto f D x₀ y₀ :=
  by
  apply MaybeUndefined.eq_defined_iff_satisfies_of_unique
  intro y₁ y₂
  apply myTendsto_unique hIn

/- Characterization of `myLim` in familiar terms -/

/- Input `x → x₀` -/

lemma myLim_pt_pt_def {α β : Type*} [MetricSpace α] [Preorder α]
  [MetricSpace β] [Nontrivial β] [PartialOrder β] [NoTopOrder β] [NoBotOrder β]
  [ClosedIciTopology β] [ClosedIicTopology β]
  {f : α → β} {D : Set α} {x₀ : α} (hx₀ : x₀ ∈ AccPts D) {y₀ : β} :
  myLim f D x₀ = y₀
    ↔  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → dist (f x) y₀ < ε :=
  by
  rw [← myTendsto_pt_pt_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_pt_iff_accPt.mpr hx₀

lemma myLim_pt_infty_def {α : Type*} [MetricSpace α] [Preorder α]
  {f : α → Number} {D : Set α} {x₀ : α} (hx₀ : x₀ ∈ AccPts D) :
  myLim f D x₀ = MaybeUndefined.of_def ∞
    ↔  ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x ≥ M :=
  by
  rw [← myTendsto_pt_infty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_pt_iff_accPt.mpr hx₀

lemma myLim_pt_neginfty_def {α : Type*} [MetricSpace α] [Preorder α]
  {f : α → Number} {D : Set α} {x₀ : α} (hx₀ : x₀ ∈ AccPts D) :
  myLim f D x₀ = MaybeUndefined.of_def -∞
    ↔  ∀ M, ∃ δ > 0, ∀ x ∈ D, (0 < dist x x₀ ∧ dist x x₀ < δ) → f x ≤ M :=
  by
  rw [← myTendsto_pt_neginfty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_pt_iff_accPt.mpr hx₀

/- Input `x → ∞` -/

lemma myLim_infty_pt_def {β : Type*} [MetricSpace β] [Nontrivial β]
  [PartialOrder β] [NoTopOrder β] [NoBotOrder β]
  [ClosedIciTopology β] [ClosedIicTopology β]
  {f : Number → β} {D : Set Number} (hD : ¬BddAbove D) {y₀ : β} :
  myLim f D ∞ = y₀  ↔  ∀ ε > 0, ∃ z, ∀ x ∈ D, x > z → dist (f x) y₀ < ε :=
  by
  rw [← myTendsto_infty_pt_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_infty_iff_notBddAbove.mpr hD

lemma myLim_infty_infty_def {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) :
  myLim f D ∞ = MaybeUndefined.of_def ∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≥ z → f x ≥ M :=
  by
  rw [← myTendsto_infty_infty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_infty_iff_notBddAbove.mpr hD

lemma myLim_infty_neginfty_def {f : Number → Number} {D : Set Number} (hD : ¬BddAbove D) :
  myLim f D ∞ = MaybeUndefined.of_def -∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≥ z → f x ≤ M :=
  by
  rw [← myTendsto_infty_neginfty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_infty_iff_notBddAbove.mpr hD

/- input `x → -∞`-/

lemma myLim_neginfty_pt_def {β : Type*} [MetricSpace β] [Nontrivial β]
  [PartialOrder β] [NoTopOrder β] [NoBotOrder β]
  [ClosedIciTopology β] [ClosedIicTopology β]
  {f : Number → β} {D : Set Number} (hD : ¬BddBelow D) {y₀ : β} :
  myLim f D -∞ = y₀  ↔  ∀ ε > 0, ∃ z, ∀ x ∈ D, x ≤ z → dist (f x) y₀ < ε :=
  by
  rw [← myTendsto_neginfty_pt_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_neginfty_iff_notBddBelow.mpr hD

lemma myLim_neginfty_infty_def {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D) :
  myLim f D -∞ = MaybeUndefined.of_def ∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≤ z → f x ≥ M :=
  by
  rw [← myTendsto_neginfty_infty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_neginfty_iff_notBddBelow.mpr hD

lemma myLim_neginfty_neginfty_def {f : Number → Number} {D : Set Number} (hD : ¬BddBelow D) :
  myLim f D -∞ = MaybeUndefined.of_def -∞  ↔  ∀ M, ∃ z, ∀ x ∈ D, x ≤ z → f x ≤ M :=
  by
  rw [← myTendsto_neginfty_neginfty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_neginfty_iff_notBddBelow.mpr hD

/- Characterization of `lim_seq` in familiar terms -/

lemma notBddAbove_natNumber : ¬BddAbove NatNumber := by
  rw [not_bddAbove_iff]
  intro x
  obtain ⟨N, _⟩ := exists_nat_gt x
  use N, ⟨N, rfl⟩

lemma lim_seq_pt_def {β : Type*} [MetricSpace β] [Nontrivial β]
  [PartialOrder β] [NoTopOrder β] [NoBotOrder β]
  [ClosedIciTopology β] [ClosedIicTopology β]
  {a : Number → β} {p : β} :
  lim_seq a = p  ↔
    ∀ ε > 0, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → dist (a n) p < ε :=
  by
  rw [← myTendsto_seq_pt_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_infty_iff_notBddAbove.mpr notBddAbove_natNumber

lemma lim_seq_infty_def {a : Number → Number} :
  lim_seq a = MaybeUndefined.of_def ∞  ↔  ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n > M :=
  by
  rw [← myTendsto_seq_infty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_infty_iff_notBddAbove.mpr notBddAbove_natNumber

lemma lim_seq_neginfty_def {a : Number → Number} :
  lim_seq a = MaybeUndefined.of_def -∞  ↔  ∀ M, ∃ N ∈ NatNumber, ∀ n ∈ NatNumber, n ≥ N → a n < M :=
  by
  rw [← myTendsto_seq_neginfty_def]
  apply myLim_iff_myTendsto
  exact neBot_inputFilter_infty_iff_notBddAbove.mpr notBddAbove_natNumber

end Characterizations


section Impossible

/- Trivial input filter implies all points satisfy convergence condition ... -/

lemma myTendsto_bot_inputFilter {α β : Type*} [TopologicalSpace α] [Preorder α]
  [TopologicalSpace β] [Preorder β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} (hIn : input_filter D x₀ = ⊥) :
  ∀ {y₀ : WithBot (WithTop β)}, myTendsto f D x₀ y₀ :=
  by
  intro y₀
  unfold myTendsto
  rw [hIn]
  apply Filter.tendsto_bot

/- ... and hence that the limit is ill-defined :) -/

lemma myLim_bot_inputFilter {α β : Type*} [TopologicalSpace α] [Preorder α]
  [TopologicalSpace β] [Preorder β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} (hIn : input_filter D x₀ = ⊥)
  {y₀ : WithBot (WithTop β)} : myLim f D x₀ ≠ y₀ :=
  by
  apply MaybeUndefined.neq_defined_of_all_satisfied
  apply myTendsto_bot_inputFilter
  exact hIn

/- Trivial output filter requires input filter to be trivial for convergence -/

lemma myTendsto_iff_bot_inputFilter_of_bot_outputFilter {α β : Type*}
  [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} {y₀ : WithBot (WithTop β)}
  (hOut : output_filter y₀ = ⊥) : myTendsto f D x₀ y₀  ↔  (input_filter D x₀ = ⊥) :=
  by
  constructor <;> intro h; swap
  · apply myTendsto_bot_inputFilter h
  contrapose hOut
  rw [← ne_eq, ← Filter.neBot_iff]
  rw [← ne_eq, ← Filter.neBot_iff] at hOut
  apply @Filter.Tendsto.neBot _ _ _ _ _ h

/- ... hence the limit is then ill-defined -/

lemma myLim_bot_outputFilter {α β : Type*}
  [TopologicalSpace α] [Preorder α] [TopologicalSpace β] [Preorder β] [Nontrivial β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} {y₀ : WithBot (WithTop β)}
  (hOut : output_filter y₀ = ⊥) : myLim f D x₀ ≠ y₀ :=
  by
  -- already seen that trivial input filter results in ill-defined limit
  wlog h : input_filter D x₀ ≠ ⊥
  · rw [not_not] at h
    apply myLim_bot_inputFilter h
  -- use previous lemma
  contrapose h
  rw [← myTendsto_iff_bot_inputFilter_of_bot_outputFilter hOut]
  apply MaybeUndefined.satisfies_of_eq_defined h

/- Limits to `∞` and `-∞` (both input and output) are ill-defined for metric spaces without
 an inherent preorder, i.e., those that get assigned the `discreteOrder`.  -/

/- Set up -/

lemma bot_atTop_discreteOrder {γ : Type*} [MetricSpace γ] [Nontrivial γ] :
  (atTop : Filter γ) = ⊥ := by
  rw [← Filter.empty_mem_iff_bot]
  have : ∃ a b : γ, a ≠ b := by rwa [← nontrivial_iff]
  obtain ⟨a, b, aneqb⟩ := this
  have : ∅ = {x | x ≥ a} ∩ {x | x ≥ b} := by
    ext x
    simp only [Set.mem_empty_iff_false, ge_iff_le, Set.mem_inter_iff, Set.mem_setOf_eq, false_iff,
      not_and]
    simp only [LE.le]
    intro h1 h2
    exact aneqb (h1.trans h2.symm)
  rw [this]
  apply Filter.inter_mem <;> apply Filter.mem_atTop

lemma bot_atBot_discreteOrder {γ : Type*} [MetricSpace γ] [Nontrivial γ] :
  (atBot : Filter γ) = ⊥ := by
  rw [← Filter.empty_mem_iff_bot]
  have : ∃ a b : γ, a ≠ b := by rwa [← nontrivial_iff]
  obtain ⟨a, b, aneqb⟩ := this
  have : ∅ = {x | x ≤ a} ∩ {x | x ≤ b} := by
    ext x
    simp only [Set.mem_empty_iff_false, Set.mem_inter_iff, Set.mem_setOf_eq, false_iff, not_and]
    simp only [LE.le]
    intro h1 h2
    exact aneqb (h1.symm.trans h2)
  rw [this]
  apply Filter.inter_mem <;> apply Filter.mem_atBot

lemma bot_inputFilter_infty_discreteOrder {α : Type*} [MetricSpace α] [Nontrivial α] {D : Set α} :
  (input_filter D ∞ : Filter α) = ⊥ := by
  simp only [input_filter]
  rw [inf_principal_eq_bot]
  rw [bot_atTop_discreteOrder]
  apply Filter.mem_bot

lemma bot_inputFilter_neginfty_discreteOrder {α : Type*} [MetricSpace α] [Nontrivial α] {D : Set α} :
  (input_filter D -∞ : Filter α) = ⊥ := by
  simp only [input_filter]
  rw [inf_principal_eq_bot]
  rw [bot_atBot_discreteOrder]
  apply Filter.mem_bot

lemma bot_outputFilter_infty_discreteOrder {β : Type*} [MetricSpace β] [Nontrivial β] :
  (output_filter ∞ : Filter β) = ⊥ := by
  simp only [output_filter]
  rw [bot_atTop_discreteOrder]

lemma bot_outputFilter_neginfty_discreteOrder {β : Type*} [MetricSpace β] [Nontrivial β] :
  (output_filter -∞ : Filter β) = ⊥ := by
  simp only [output_filter]
  rw [bot_atBot_discreteOrder]

/- Concrete results -/

lemma myLim_neq_input_infty_metricSpace {α β : Type*} [MetricSpace α] [Nontrivial α]
  [TopologicalSpace β] [Preorder β]
  {f : α → β} {D : Set α} {y₀ : WithBot (WithTop β)} : myLim f D ∞ ≠ (y₀) :=
  by
  apply myLim_bot_inputFilter
  apply bot_inputFilter_infty_discreteOrder

lemma myLim_neq_input_neginfty_metricSpace {α β : Type*} [MetricSpace α] [Nontrivial α]
  [TopologicalSpace β] [Preorder β]
  {f : α → β} {D : Set α} {y₀ : WithBot (WithTop β)} : myLim f D -∞ ≠ (MaybeUndefined.of_def y₀) :=
  by
  apply myLim_bot_inputFilter
  apply bot_inputFilter_neginfty_discreteOrder

lemma myLim_neq_output_infty_metricSpace {α β : Type*} [TopologicalSpace α] [Preorder α]
  [MetricSpace β] [Nontrivial β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} : myLim f D x₀ ≠ (MaybeUndefined.of_def ∞) :=
  by
  apply myLim_bot_outputFilter
  apply bot_outputFilter_infty_discreteOrder

lemma myLim_neq_output_neginfty_metricSpace {α β : Type*} [TopologicalSpace α] [Preorder α]
  [MetricSpace β] [Nontrivial β]
  {f : α → β} {D : Set α} {x₀ : WithBot (WithTop α)} : myLim f D x₀ ≠ (MaybeUndefined.of_def -∞) :=
  by
  apply myLim_bot_outputFilter
  apply bot_outputFilter_neginfty_discreteOrder

/- and for sequences -/

lemma limseq_neq_infty_metricSpace {β : Type*} [MetricSpace β] [Nontrivial β]
  {a : Number → β} : lim_seq a ≠ MaybeUndefined.of_def ∞ := by
  apply myLim_neq_output_infty_metricSpace


lemma limseq_neq_neginfty_metricSpace {β : Type*} [MetricSpace β] [Nontrivial β]
  {a : Number → β} : lim_seq a ≠ MaybeUndefined.of_def -∞ := by
  apply myLim_neq_output_neginfty_metricSpace

-- TODO: maybe `Nontrivial β` requirement can be removed for `myLim` and `lim_seq`
-- reason: if `β` has only one term, both `-∞` and `∞` will be valid limit points,
--   hence the limit is ill-defined

end Impossible


section Laws

-- WIP

end Laws


section Example

-- theorem lim_seq_divn_zero : lim_seq (fun n ↦ 1/n) = 0 := by sorry
theorem lim_seq_divn_zero : lim_seq (fun n ↦ 1/n) = MaybeUndefined.of_def 0 := by sorry

open WithBotTop
#check MaybeUndefined.of_def (∞ : [-∞,∞]) + MaybeUndefined.of_def (∞ : [-∞,∞])

lemma computation₁ : lim_seq (fun n ↦ 1 + 1/n) = MaybeUndefined.of_def 1 := by
  calc
    lim_seq (fun n ↦ 1 + 1/n)
      = lim_seq (fun n ↦ 1) + lim_seq (fun n ↦ 1/n) := by sorry
    _ = 1 + lim_seq (fun n ↦ 1/n) := by sorry
    _ = 1 + 0 := by rw [lim_seq_divn_zero]
    _ = 1 := by sorry

lemma corollary₁ : myTendsto (fun n ↦ 1 + 1/n) NatNumber ∞ 1 :=
  MaybeUndefined.satisfies_of_eq_defined computation₁


-- #synth Add (MaybeUndefined (WithBot (WithTop ℝ)))
-- #check WithBotTop.add_conservative



-- lemma computation₂ : lim_seq (fun n ↦ 2 + 1/n) = MaybeUndefined.of_def (1 + 1) := by
--   calc
--     lim_seq (fun n ↦ 2 + 1/n)
--       = lim_seq (fun n ↦ 2) + lim_seq (fun n ↦ 1/n) := by sorry
--     _ = 2 + lim_seq (fun n ↦ 1/n) := by sorry
--     _ = 2 + 0 := by rw [lim_seq_divn_zero]
--     _ = 1 + 1 := by sorry

-- lemma corollary₂ : myTendsto (fun n ↦ 2 + 1/n) NatNumber ∞ (1 + 1) :=
--   MaybeUndefined.satisfies_of_eq_defined computation₂

end Example

end Limit
