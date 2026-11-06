import Mathlib

theorem inequalities_169445 (x : ℝ) (hx : x > 0) :
    3 ≤ 1 / x + 4 * x ^ 2 := by
  have h1 : 1 / x + 4 * x ^ 2 - 3 ≥ 0 := by 
    have h2 : x > 0 := hx
    have h3 : 1 / x + 4 * x ^ 2 - 3 = (1 + 4 * x ^ 3 - 3 * x) / x := by
      field_simp
      <;> ring
    rw [h3] at *
    have h4 : 1 + 4 * x ^ 3 - 3 * x ≥ 0 := by 
      nlinarith [sq_nonneg (x - 1/2), sq_nonneg (2 * x - 1), 
          sq_nonneg (x + 1), 
          sq_nonneg (x * (x + 1)), 
          mul_pos (show (0 : ℝ) < x by linarith) (show (0 : ℝ) < x by linarith),
          sq_nonneg (4 * x - 2)]
    have h5 : (1 + 4 * x ^ 3 - 3 * x) ≥ 0 := by linarith
    have h6 : (1 + 4 * x ^ 3 - 3 * x) / x ≥ 0 := by 
      apply div_nonneg
      linarith
      linarith
    linarith
  linarith [h1]