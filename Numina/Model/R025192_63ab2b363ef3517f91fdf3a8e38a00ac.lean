import Mathlib.Tactic

theorem inequalities_600069
    (x y z : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hz : 0 ≤ z)
    (hsum : x + y + z = 2) :
    x^2 * y^2 + y^2 * z^2 + z^2 * x^2 + x * y * z ≤ 1 := by
  have h6 : z = 2 - x - y := by linarith
  rw [h6] at *
  -- new approach
  -- bound z ≥ 0
  have h7 : 0 ≤ 2 - x - y := by nlinarith
  -- bounds for variables
  have h9 : x ≤ 2 := by
    nlinarith
  have h10 : y ≤ 2 := by
    nlinarith
  -- products ≥ 0
  have h11 : x * y ≥ 0 := by
    apply mul_nonneg
    linarith
    linarith
  -- xz ≥ 0, yz ≥ 0
  have h12 : x * (2 - x - y) ≥ 0 := by
    apply mul_nonneg
    linarith
    linarith
  have h13 : y * (2 - x - y) ≥ 0 := by
    apply mul_nonneg
    linarith
    linarith
  -- squares of intermidiate expressions
  nlinarith [sq_nonneg (x - y), sq_nonneg (x - (2 - x - y)), sq_nonneg (y - (2 - x - y)), 
          sq_nonneg (x * y - (2 - x - y)), sq_nonneg (x + y - 1), sq_nonneg ((2 - x - y) - 1), 
          mul_nonneg hx hy, 
          mul_nonneg hx (show (0 : ℝ) ≤ (2 - x - y) by nlinarith), 
          mul_nonneg (show (0 : ℝ) ≤ (2 - x - y) by nlinarith) hy 
          ]