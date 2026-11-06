import Mathlib

theorem algebra_294433 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : 1 / (2 * x + y) + 1 / (y + 1) = 1) :
    x + 2 * y ≥ Real.sqrt 3 + 1 / 2 := by 
  have h1 : 0 < (2 * x + y) := by
    nlinarith [show 0 < x by linarith, show 0 < y by linarith]
  have h2 : 0 < (y + 1) := by
    nlinarith [show 0 < y by linarith]

  have h_eq : 2 * x * y + y ^ 2 - y - 1 = 0 := by
    have h3 : (2 * x + y) ≠ 0 := by linarith
    have h4 : (y + 1) ≠ 0 := by linarith
    field_simp [h3, h4] at h
    nlinarith

  nlinarith [sq_nonneg (x + 2 * y - (Real.sqrt 3 + 1 / 2)), 
          sq_nonneg (y - Real.sqrt 3 / 3), 
          sq_nonneg (x - (Real.sqrt 3 / 3 + 1 / 2)), 
          Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith), 
          sq_nonneg ( (2 * x + y) * (y + 1) ), 
          h_eq, 
          mul_pos hx hy, 
          sq_nonneg ( (y - Real.sqrt 3 / 3) ), 
          sq_nonneg (x - (Real.sqrt 3 / 3 + 1 / 2) ) ]