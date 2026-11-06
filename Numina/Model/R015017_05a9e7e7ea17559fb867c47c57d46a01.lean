import Mathlib

theorem algebra_247121 {P : Polynomial ℝ} (hP : ∀ x : ℝ, abs x ≤ 1 → P.eval (x * Real.sqrt 2) = P.eval (x + Real.sqrt (1 - x^2))) :
    ∃ f : ℝ → ℝ, ∀ x : ℝ, P.eval x = f (x / Real.sqrt 2) := by

  use fun t ↦ P.eval (t * Real.sqrt 2)
  intro x
  have h1 : (x / Real.sqrt 2) * Real.sqrt 2 = x := by
    field_simp [Real.sqrt_ne_zero']
    <;> linarith [Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0)]
  simp [h1]