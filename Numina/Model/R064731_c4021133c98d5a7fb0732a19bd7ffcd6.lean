import Mathlib

theorem algebra_1030 (x y : ℝ) (hx : 0 < x) (hy : x < 1) (hxy : 1 < y) (hyy : y < 2) :
    Real.sqrt (x ^ 2 + y ^ 2 - 2 * x * y + 4 * x - 4 * y + 4) +
    Real.sqrt (1 - 2 * x + x ^ 2) - Real.sqrt (y ^ 2 - 4 * y + 4) = 1 := by
  have h1 : Real.sqrt (x ^ 2 + y ^ 2 - 2 * x * y + 4 * x - 4 * y + 4) = Real.sqrt ((x - y + 2) ^ 2) := by
    ring_nf
  have h2 : Real.sqrt ((x - y + 2) ^ 2) = x - y + 2 := by
    rw [Real.sqrt_sq_eq_abs]
    have h3 : y < x + 2 := by linarith
    have h4 : x - y + 2 > 0 := by linarith
    rw [abs_of_pos h4]
  have h5 : Real.sqrt (1 - 2 * x + x ^ 2) = Real.sqrt ((x - 1) ^ 2) := by
    ring_nf
  have h6 : Real.sqrt ((x - 1) ^ 2) = 1 - x := by
    rw [Real.sqrt_sq_eq_abs]
    have h7 : x - 1 < 0 := by linarith
    rw [abs_of_neg h7]
    ring
  have h8 : Real.sqrt (y ^ 2 - 4 * y + 4) = Real.sqrt ((y - 2) ^ 2) := by
    ring_nf
  have h9 : Real.sqrt ((y - 2) ^ 2) = 2 - y := by
    rw [Real.sqrt_sq_eq_abs]
    have h10 : y - 2 < 0 := by linarith
    rw [abs_of_neg h10]
    ring
  rw [h1, h2, h5, h6, h8, h9]
  all_goals nlinarith