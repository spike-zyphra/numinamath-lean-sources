import Mathlib

theorem inequalities_81198 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    (1 + 1 / x) * (1 + 1 / y) ≥ 9 := by
  have hy1 : y = 1 - x := by linarith
  rw [hy1]
  have h1 : x * (1 - x) ≤ (1 / 4 : ℝ) := by
    nlinarith [sq_nonneg (x - 1 / 2), mul_pos hx (show (0 : ℝ) < (1 - x) by nlinarith)]
  have h2 : x > 0 := by linarith
  have h3 : 1 - x > 0 := by nlinarith
  have h4 : x * (1 - x) > 0 := by 
    nlinarith
  have h5 : (1 + 1 / x) * (1 + 1 / (1 - x)) ≥ 9 := by 
    have h6 : (1 + 1 / x) * (1 + 1 / (1 - x)) - 9 ≥ 0 := by 
      have h6 : (1 + 1 / x) * (1 + 1 / (1 - x)) - 9 =
        ((x + 1) * (2 - x) - 9 * x * (1 - x)) / (x * (1 - x)) := by
        field_simp
        ring
      rw [h6]
      apply div_nonneg 
      nlinarith [sq_nonneg (x - 1 / 2)]
      all_goals nlinarith 
    linarith 
  linarith [h5]