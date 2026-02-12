import Mathlib.Data.Option.Basic
-- import Mathlib.Data.Option.Defs
-- import Mathlib.Data.Set.Basic
import Mathlib.Tactic.ToAdditive
import Mathlib.Tactic.WLOG

def MaybeUndefined (α : Type*) := Option α

-- notation
-- postfix:max "??" => MaybeUndefined

namespace MaybeUndefined

open Classical in
noncomputable def unique_satisfier {α : Type*} (P : α → Prop) : MaybeUndefined α :=
  if h : ∃! x : α, P x then some (Exists.choose h) else none
def of_def {α : Type*} (x : α) : MaybeUndefined α := some x

instance {α : Type*} : CoeTail α (MaybeUndefined α) where
  coe := of_def


/- Establish key properties of `MaybeUndefined α`
(theorem names can be improved) -/

/- From newer version MathLib (TODO: remove) -/
theorem ExistsUnique.choose_eq_iff {α : Type*} {p : α → Prop} {a : α} (h : ∃! x, p x) :
    h.choose = a ↔ p a :=
  ⟨fun ha ↦ ha ▸ h.choose_spec.left, h.unique h.choose_spec.left⟩

lemma satisfies_of_eq_defined {α : Type*} {P : α → Prop} {x : α}
  (h : unique_satisfier P = x) : P x := by
  unfold unique_satisfier of_def at h
  wlog hex : ∃! x', P x'
  · rw [dif_neg hex] at h; contradiction -- contradiction from `none = some x`
  rw [dif_pos hex] at h
  rw [Option.some_inj] at h
  rwa [ExistsUnique.choose_eq_iff] at h

lemma unique_satisfies_of_eq_defined {α : Type*} {P : α → Prop} {x y : α}
  (h : unique_satisfier P = x) (hy : P y) : y = x := by
  unfold unique_satisfier of_def at h
  wlog hex : ∃! x', P x'
  · rw [dif_neg hex] at h; contradiction -- contradiction from `none = some x`
  apply hex.unique hy
  apply satisfies_of_eq_defined h

lemma eq_defined_of_unique_of_satisfies {α : Type*} {P : α → Prop} {x : α}
  (hx : P x) (hunique : ∀ {y z}, P y → P z → y = z) : unique_satisfier P = x := by
  have hex : ∃! x, P x := ⟨x, hx, fun y hy ↦ hunique hy hx⟩
  unfold unique_satisfier of_def
  rw [dif_pos hex]
  congr
  rwa [ExistsUnique.choose_eq_iff]

theorem eq_defined_iff_satisfies_of_unique {α : Type*} {P : α → Prop} {x : α}
  (hunique : ∀ {y z}, P y → P z → y = z) : unique_satisfier P = x ↔ P x := by
  constructor <;> intro h
  · exact satisfies_of_eq_defined h
  · exact eq_defined_of_unique_of_satisfies h hunique

lemma neq_defined_of_separate_satisfied {α : Type*} {P : α → Prop} {x₁ x₂ : α}
  (hneq : x₁ ≠ x₂) (h₁ : P x₁) (h₂ : P x₂) {x : α} : unique_satisfier P ≠ x := by
  intro hx
  have x₁eqx : x₁ = x := by exact unique_satisfies_of_eq_defined hx h₁
  have x₂eqx : x₂ = x := by exact unique_satisfies_of_eq_defined hx h₂
  exact hneq (x₁eqx.trans x₂eqx.symm)

theorem neq_defined_of_all_satisfied {α : Type*} [Nontrivial α] {P : α → Prop}
  (hall : ∀ y : α, P y) {x : α} : unique_satisfier P ≠ x := by
  have : ∃ x₁ x₂ : α, x₁ ≠ x₂ := by rwa [← nontrivial_iff]
  obtain ⟨x₁, x₂, x₁neqx₂⟩ := this
  exact neq_defined_of_separate_satisfied x₁neqx₂ (hall x₁) (hall x₂)

end MaybeUndefined



-- /- Inherited operations -/
-- section MaybeUndefined.Operations

-- -- @[to_additive]
-- -- protected def MaybeUndefined.one {α : Type*} [One α] : One (MaybeUndefined α) :=
-- --   ⟨of_defined 1⟩

-- -- attribute [instance] MaybeUndefined.one MaybeUndefined.zero

-- @[to_dual]
-- protected def MaybeUndefined.top {α : Type*} [Top α] : Top (MaybeUndefined α) :=
--   ⟨of_def Top.top⟩

-- attribute [instance] MaybeUndefined.top MaybeUndefined.bot

-- @[to_additive]
-- protected def MaybeUndefined.mul {α : Type*} [Mul α] : Mul (MaybeUndefined α) :=
--   ⟨Set.image2 Mul.mul⟩

-- attribute [instance] MaybeUndefined.mul MaybeUndefined.add

-- @[to_additive]
-- protected def MaybeUndefined.inv {α : Type*} [Inv α] : Inv (MaybeUndefined α) :=
--   ⟨Set.image Inv.inv⟩

-- attribute [instance] MaybeUndefined.inv MaybeUndefined.neg

-- @[to_additive]
-- protected def MaybeUndefined.div {α : Type*} [Div α] : Div (MaybeUndefined α) :=
--   ⟨Set.image2 Div.div⟩

-- attribute [instance] MaybeUndefined.div MaybeUndefined.sub

-- -- TODO add instance (?) that these indeed satisfy the required properties for these rules
-- -- i.e. that `of_defined '' α` has the same structure as `α`
