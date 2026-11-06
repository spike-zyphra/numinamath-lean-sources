import Mathlib

open Real

theorem inequalities_318359 : ¬ (∀ a b : ℝ, 0 < a → 0 < b → 2 / (1 / a + 1 / b) ≥ sqrt (a * b)) := by
  intro h
  have h1 := h 1 4 (by norm_num) (by norm_num)
  have h2 : 2 / (1 / (1 : ℝ) + 1 / (4 : ℝ)) < sqrt ((1 : ℝ) * (4 : ℝ)) := by
    have h3 : 2 / (1 / (1 : ℝ) + 1 / (4 : ℝ)) = (8 / 5 : ℝ) := by
      norm_num
    have h4 : sqrt ((1 : ℝ) * (4 : ℝ)) = (2 : ℝ) := by
      have h5 : (1 : ℝ) * (4 : ℝ) = (4 : ℝ) := by norm_num
      rw [h5]
      rw [Real.sqrt_eq_cases]
      norm_num
    rw [h3, h4]
    all_goals norm_num
  linarith