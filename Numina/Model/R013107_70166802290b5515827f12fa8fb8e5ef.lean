import Mathlib

theorem inequalities_308928 (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i)
    (h : ∑ i, 1 / (1 + x i) = 1) :
    ∑ i in Finset.range 3, x i / (4 + (x i)^2) ≤ 1 := by

  have h1 : x 0 / (4 + (x 0)^2) ≤ 1 / 4 := by
    have h2 : 0 < x 0 := hx 0
    have h3 : 0 < 4 + (x 0) ^ 2 := by nlinarith [h2, sq_pos_of_pos h2]
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    nlinarith [sq_nonneg (x 0 - 2), mul_pos h2 (show 0 < (4 : ℝ) by linarith)]

  have h2 : x 1 / (4 + (x 1)^2) ≤ 1 / 4 := by
    have h4 : 0 < x 1 := hx 1
    have h5 : 0 < 4 + (x 1) ^ 2 := by nlinarith [h4, sq_pos_of_pos h4]
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    nlinarith [sq_nonneg (x 1 - 2), mul_pos h4 (show 0 < (4 : ℝ) by linarith)]

  have h3 : x 2 / (4 + (x 2)^2) ≤ 1 / 4 := by
    have h4 : 0 < x 2 := hx 2
    have h5 : 0 < 4 + (x 2) ^ 2 := by nlinarith [h4, sq_pos_of_pos h4]
    apply (div_le_div_iff (by linarith) (by linarith)).mpr
    nlinarith [sq_nonneg (x 2 - 2), mul_pos h4 (show 0 < (4 : ℝ) by linarith)]

  have h4 : ∑ i in Finset.range 3, x i / (4 + (x i)^2) = x 0 / (4 + (x 0)^2) + x 1 / (4 + (x 1)^2) + x 2 / (4 + (x 2)^2) := by
    simp [Finset.sum_range_succ]

  rw [h4]
  linarith [h1, h2, h3]