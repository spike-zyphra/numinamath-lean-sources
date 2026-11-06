import Mathlib

open Real

theorem algebra_159893 {x : ℝ} (hx : x ≠ 0) :
    sqrt (1 + ((x ^ 2 - 1) / (2 * x)) ^ 2) / ((x ^ 2 + 1) * (1 / x)) =
    if x < 0 then -1 / 2 else 1 / 2 := by
  have h1 : sqrt (1 + ((x ^ 2 - 1) / (2 * x)) ^ 2) = (x ^ 2 + 1) / (2 * |x|) := by
    have h2 : 1 + ((x ^ 2 - 1) / (2 * x)) ^ 2 = ((x ^ 2 + 1) ^ 2) / (4 * x ^ 2) := by
      field_simp
      ring
    rw [h2]
    have h3 : sqrt (((x ^ 2 + 1) ^ 2) / (4 * x ^ 2)) = (x ^ 2 + 1) / (2 * |x|) := by
      have h4 : sqrt (((x ^ 2 + 1) ^ 2) / (4 * x ^ 2)) = sqrt ((x ^ 2 + 1) ^ 2) / sqrt (4 * x ^ 2) := by
        rw [Real.sqrt_div (by
          have : 4 * x ^ 2 > 0 := by
            have h1 : x ^ 2 > 0 := by
              exact sq_pos_of_ne_zero hx
            nlinarith
          positivity
        )]
      rw [h4]
      have h5 : sqrt ((x ^ 2 + 1) ^ 2) = x ^ 2 + 1 := by
        rw [Real.sqrt_sq (show 0 ≤ x ^ 2 + 1 by positivity)]
      have h6 : sqrt (4 * x ^ 2) = 2 * |x| := by
        have h7 : sqrt (4 * x ^ 2) = sqrt (4) * sqrt (x ^ 2) := by
          rw [Real.sqrt_mul (by
            have : x ^ 2 ≥ 0 := by positivity
            nlinarith
          )]
        have h8 : sqrt (4 : ℝ) = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
        have h9 : sqrt (x ^ 2 : ℝ) = |x| := by
          rw [Real.sqrt_sq_eq_abs]
        rw [h7, h8, h9]
      rw [h5, h6]
      all_goals ring
    exact h3
  have h2 : sqrt (1 + ((x ^ 2 - 1) / (2 * x)) ^ 2) / ((x ^ 2 + 1) * (1 / x)) = x / (2 * |x|) := by
    rw [h1]
    have h3 : (x ^ 2 + 1) * (1 / x) = (x ^ 2 + 1) / x := by
      field_simp
    rw [h3]
    have h4 : x ^ 2 + 1 ≠ 0 := by
      have h11 : x ^ 2 ≥ 0 := sq_nonneg x
      nlinarith
    field_simp [h4, hx]
    all_goals ring
  rw [h2]
  split_ifs with h
  · -- x < 0
    have h3 : |x| = -x := abs_of_neg h
    rw [h3]
    field_simp [show x ≠ 0 by exact hx]
    all_goals nlinarith
  · -- x ≥ 0
    have h4 : x ≥ 0 := by linarith
    have h6 : |x| = x := abs_of_nonneg (show 0 ≤ x by linarith)
    rw [h6]
    field_simp [show x ≠ 0 by exact hx]
    all_goals nlinarith