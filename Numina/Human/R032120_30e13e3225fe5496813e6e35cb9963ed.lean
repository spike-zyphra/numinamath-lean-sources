import Mathlib

open Real Filter Function
open scoped Topology

theorem calculus_279245 :
    (∀ a : ℝ, 1 < a → Tendsto (logb a) atTop atTop ∧ Tendsto (logb a) (𝓝[>] 0) atBot) ∧
    (∀ a : ℝ, 0 < a ∧ a < 1 → Tendsto (logb a) atTop atBot ∧ Tendsto (logb a) (𝓝[>] 0) atTop) := by
  constructor
  . intro a ha
    constructor
    exact tendsto_logb_atTop ha
    exact tendsto_logb_nhdsWithin_zero_right ha
  . intro a ⟨ha₁, ha₂⟩
    constructor
    exact tendsto_logb_atTop_of_base_lt_one ha₁ ha₂
    exact tendsto_logb_nhdsWithin_zero_right_of_base_lt_one ha₁ ha₂
