import Mathlib

theorem algebra_167373 (x : ℝ) (hx : x = 5 / 2) :
    2^(x + Real.sqrt (x^2 - 4)) - 5 * (Real.sqrt 2)^(x - 2 + Real.sqrt (x^2 - 4)) - 6 = 0 := by
  rw [hx]
  have h1 : (5 / 2 : ℝ) ^ 2 - (4 : ℝ) = (9 / 4 : ℝ) := by
    norm_num
  have h2 : Real.sqrt ((5 / 2 : ℝ) ^ 2 - (4 : ℝ)) = (3 / 2 : ℝ) := by
    rw [h1]
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  have h3 : (5 / 2 : ℝ) + Real.sqrt ((5 / 2 : ℝ) ^ 2 - (4 : ℝ)) = (4 : ℝ) := by
    rw [h2]
    norm_num
  have h4 : (5 / 2 : ℝ) - (2 : ℝ) + Real.sqrt ((5 / 2 : ℝ) ^ 2 - (4 : ℝ)) = (2 : ℝ) := by
    rw [h2]
    norm_num
  rw [h3, h4]
  have h5 : (2 : ℝ) ^ ((4 : ℝ)) - 5 * (Real.sqrt 2) ^ ((2 : ℝ)) - 6 = 0 := by
    have h6 : (2 : ℝ) ^ ((4 : ℝ)) = (16 : ℝ) := by
      norm_num
    have h7 : (Real.sqrt 2) ^ ((2 : ℝ)) = (2 : ℝ) := by
      have h8 : (Real.sqrt 2 : ℝ) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
      exact_mod_cast h8
    rw [h6, h7]
    norm_num
  exact_mod_cast h5