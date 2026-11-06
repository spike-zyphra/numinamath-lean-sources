import Mathlib
open Real
theorem inequalities_5173 (x : ℝ) (hx : x > 3) :
    sqrt x + 6 / (x - 3) ≥ 4 := by
  have h1 : sqrt x > 0 := by
    apply sqrt_pos.2
    linarith
  have h2 : x - 3 > 0 := by
    linarith
  have h3 : sqrt x ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : sqrt x + 6 / (x - 3) - 4 ≥ 0 := by
    have h5 : x - 3 > 0 := h2
    have h6 : sqrt x + 6 / (x - 3) - 4 = (sqrt x * (x - 3) + 6 - 4 * (x - 3)) / (x - 3) := by
      field_simp [show x - 3 ≠ 0 by linarith]
      <;> ring
    rw [h6]
    apply div_nonneg
    nlinarith [sq_nonneg (sqrt x - 3), sq_nonneg (x - 9), 
      sq_nonneg (sqrt x ^ 2 - 3), 
      Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)
    ]
    all_goals
      nlinarith
  linarith [h4]