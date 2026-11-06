import Mathlib

open Real

theorem algebra_4840 {x : ℝ} (hx : x = 102 * sqrt (2023 + 102 * sqrt (2023 + x))) :
    sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + x)))) = 119 := by
  have h1 : sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + x)))) = 119 := by
    have hx1 : 0 ≤ 2023 + x := by nlinarith [show 0 ≤ x from by nlinarith [Real.sqrt_nonneg (2023 + 102 * sqrt (2023 + x)), hx, Real.sqrt_nonneg (2023 + x)], Real.sqrt_nonneg (2023 + x)]
    have hx2 : 0 ≤ 2023 + 102 * sqrt (2023 + x) := by nlinarith [Real.sqrt_nonneg (2023 + x)]
    have hx3 : 0 ≤ 102 * sqrt (2023 + 102 * sqrt (2023 + x)) := by nlinarith [Real.sqrt_nonneg (2023 + 102 * sqrt (2023 + x)), Real.sqrt_nonneg (2023 + x)]
    have h2 : sqrt (2023 + x) = 119 := by
      have hx1 : 0 ≤ 2023 + x := by nlinarith [show 0 ≤ x from by nlinarith [Real.sqrt_nonneg (2023 + 102 * sqrt (2023 + x)), hx, Real.sqrt_nonneg (2023 + x)], Real.sqrt_nonneg (2023 + x)]
      have eq1 : x = 102 * sqrt (2023 + 102 * sqrt (2023 + x)) := hx
      have eq2 : sqrt (2023 + x) = 119 := by
        nlinarith [sq_sqrt (show (0 : ℝ) ≤ 2023 + x by nlinarith), sq_sqrt (show (0 : ℝ) ≤ 2023 + 102 * sqrt (2023 + x) by nlinarith [Real.sqrt_nonneg (2023 + x)]), Real.sqrt_nonneg (2023 + x), Real.sqrt_nonneg (2023 + 102 * sqrt (2023 + x)), sq_nonneg (sqrt (2023 + 102 * sqrt (2023 + x)) - 119), sq_nonneg (sqrt (2023 + x) - 119)]
      exact eq2
    have h3 : sqrt (2023 + 102 * sqrt (2023 + x)) = 119 := by
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + x))) = 119 := by
      rw [h3]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h5 : sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + 102 * sqrt (2023 + x)))) = 119 := by
      rw [h4]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    exact h5
  exact h1