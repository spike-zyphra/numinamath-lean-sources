import Mathlib

theorem number_theory_212160 (x y : ℤ) :
    ∃ q : ℚ, Real.sqrt ((3 * x - 4 * y + 4) ^ 2) / Real.sqrt (3 ^ 2 + (-4) ^ 2) = q := by
  use (abs (3 * x - 4 * y + 4) : ℚ) / 5
  have h1 : Real.sqrt ((3 * x - 4 * y + 4 : ℝ) ^ 2) = abs ((3 * x - 4 * y + 4 : ℝ)) := by
    rw [Real.sqrt_sq_eq_abs]
  have h2 : Real.sqrt ((3 ^ 2 + (-4 : ℝ) ^ 2) ) = (5 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : (abs ((3 * x - 4 * y + 4 : ℝ)) : ℝ) = (abs (3 * x - 4 * y + 4 : ℤ) : ℝ) := by 
    simp
  rw [h1, h2, h3]
  all_goals norm_num
  all_goals norm_num