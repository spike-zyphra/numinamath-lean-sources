import Mathlib

open Real

theorem algebra_4884 {f g : ℝ → ℝ} (hf : f = λ x => 3 - sqrt x)
    (hg : g = λ x => 5 * x + 2 * x ^ 2) : f (g (-5)) = -2 := by
  have h1 : g (-5) = 25 := by
    rw [hg]
    norm_num
  have h2 : f 25 = -2 := by
    rw [hf]
    have h3 : sqrt (25 : ℝ) = 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    simp [h3]
    all_goals norm_num
  rw [h1]
  exact h2