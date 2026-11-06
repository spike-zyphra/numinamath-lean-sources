import Mathlib

theorem algebra_104742 (a b c d m : ℝ) (ha : b = m * a + k) (hc : d = m * c + k) :
    Real.sqrt ((a - c)^2 + (b - d)^2) = |a - c| * Real.sqrt (1 + m^2) := by
  have h1 : b - d = m * (a - c) := by
    rw [ha, hc]
    linarith
  have h2 : (a - c)^2 + (b - d)^2 = (a - c)^2 * (1 + m^2) := by
    rw [h1]
    ring
  rw [h2]
  have h3 : Real.sqrt ((a - c)^2 * (1 + m^2)) = Real.sqrt ((a - c)^2) * Real.sqrt (1 + m^2) := by
    rw [Real.sqrt_mul (by positivity)]
  have h4 : Real.sqrt ((a - c)^2) = |a - c| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h3, h4]
  all_goals norm_num [Real.sqrt_nonneg]
  all_goals tauto