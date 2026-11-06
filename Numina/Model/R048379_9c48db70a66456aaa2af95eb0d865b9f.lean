import Mathlib

theorem inequalities_180741 (a b c : ℝ) : (1 / 4) * a^2 + b^2 + c^2 ≥ a * b - a * c + 2 * b * c := by 
  suffices (1 / 4) * (a - 2 * (b - c))^2 ≥ 0 by linarith
  apply mul_nonneg
  norm_num
  apply pow_two_nonneg