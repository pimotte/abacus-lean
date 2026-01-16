import Mathlib.Data.Set.Basic
import Mathlib.Tactic.ToAdditive

def MaybeUndefined (α : Type*) := Set α
/- `Set α` instead of `α → Prop` because this gives lots of nice infrastructure for free,
such as `Set.singleton` and `Set.map2` -/

-- notation
-- postfix:max "??" => MaybeUndefined

namespace MaybeUndefined

@[ext]
theorem ext {α : Type*} {P Q : MaybeUndefined α} (h : ∀ x : α, P x ↔ Q x) : P = Q :=
  funext (fun x ↦ propext (h x))

def mk {α : Type*} (P : α → Prop) : MaybeUndefined α := P
def of_def {α : Type*} (x : α) : MaybeUndefined α := Set.singleton x

instance {α : Type*} : Coe α (MaybeUndefined α) where
  coe := of_def


/- Establish key properties of `MaybeUndefined α`
(theorem names can be improved) -/

lemma satisfies_of_eq_defined {α : Type*} {P : α → Prop} {x : α}
  (h : mk P = x) : P x := by
  unfold mk of_def Set.singleton at h
  rw [h]
  rfl

lemma unique_satisfies_of_eq_defined {α : Type*} {P : α → Prop} {x y : α}
  (h : mk P = x) (hy : P y) : y = x := by
  unfold mk of_def Set.singleton at h
  rwa [h] at hy

lemma eq_defined_of_unique_of_satisfies {α : Type*} {P : α → Prop} {x : α}
  (hx : P x) (hunique : ∀ {y z}, P y → P z → y = z) : mk P = x := by
  ext y
  constructor <;> intro hy
  · exact hunique hy hx
  · rwa [hy]

theorem eq_defined_iff_satisfies_of_unique {α : Type*} {P : α → Prop} {x : α}
  (hunique : ∀ {y z}, P y → P z → y = z) : mk P = x ↔ P x := by
  constructor <;> intro h
  · exact satisfies_of_eq_defined h
  · exact eq_defined_of_unique_of_satisfies h hunique

lemma neq_defined_of_separate_satisfied {α : Type*} {P : α → Prop} {x₁ x₂ : α}
  (hneq : x₁ ≠ x₂) (h₁ : P x₁) (h₂ : P x₂) {x : α} : mk P ≠ x := by
  intro hx
  have x₁eqx : x₁ = x := by exact unique_satisfies_of_eq_defined hx h₁
  have x₂eqx : x₂ = x := by exact unique_satisfies_of_eq_defined hx h₂
  exact hneq (x₁eqx.trans x₂eqx.symm)

theorem neq_defined_of_all_satisfied {α : Type*} [Nontrivial α] {P : α → Prop}
  (hall : ∀ y : α, P y) {x : α} : mk P ≠ x := by
  have : ∃ x₁ x₂ : α, x₁ ≠ x₂ := by rwa [← nontrivial_iff]
  obtain ⟨x₁, x₂, x₁neqx₂⟩ := this
  exact neq_defined_of_separate_satisfied x₁neqx₂ (hall x₁) (hall x₂)

end MaybeUndefined



-- -- /- Establish inherited arithmetic operations -/
-- -- section MaybeUndefined.Operations

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
