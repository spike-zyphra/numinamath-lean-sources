import Mathlib

theorem algebra_4576 {x : ℤ} (hx1 : x > 0) (hx2 : (x^2 + x + 1 : ℝ) / (x^2 + 1) + (3 * x^2 + 2 * x + 3 : ℝ) / (x^2 + x + 1) = 529 / 130) : x = 3 := by
  have eq1 : x ≤ 10 := by
    by_contra h
    push_neg at h
    have h1 : x ≥ 11 := by omega
    have eq2 := hx2
    have h3 : (x : ℝ) > 0 := by
      exact_mod_cast (show (x : ℝ) > 0 by exact_mod_cast hx1)
    have h4 : (x : ℝ) ≥ 11 := by
      exact_mod_cast h1
    field_simp at eq2
    ring_nf at eq2
    nlinarith [sq_nonneg ((x : ℝ) - 3), sq_nonneg ((x : ℝ) + 3), sq_nonneg ((x : ℝ) - 1), sq_nonneg ((x : ℝ) + 1), sq_nonneg ((x : ℝ) ^ 2 - 9), sq_nonneg ((x : ℝ) ^ 2 - 1), sq_nonneg ((x : ℝ) ^ 2 - 4), sq_nonneg ((x : ℝ) ^ 2 - 16)]
  interval_cases x <;> norm_num at hx2 <;> all_goals
    linarith