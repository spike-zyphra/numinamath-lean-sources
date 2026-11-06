import Mathlib

theorem algebra_264642 {x y : ℝ} (h1 : Real.sqrt ((x + 4)^2) = 4 - y) (h2 : Real.sqrt ((y - 4)^2) = x + 8) :
    (x, y) = (-6, 2) := by
  have eq1 : Real.sqrt ((x + 4) ^ 2) = |x + 4| := by
    rw [Real.sqrt_sq_eq_abs]
  have eq2 : Real.sqrt ((y - 4) ^ 2) = |y - 4| := by
    rw [Real.sqrt_sq_eq_abs]
  rw [eq1] at h1
  rw [eq2] at h2
  by_cases h3 : x + 4 ≥ 0
  · -- case where x + 4 ≥ 0
    rw [abs_of_nonneg h3] at h1
    by_cases h4 : y - 4 ≥ 0
    · -- case where y - 4 ≥ 0
      rw [abs_of_nonneg (show y - 4 ≥ 0 by linarith [h4]) ] at h2
      have h5 : y = -x := by linarith
      have h6 : x = -6 := by
        linarith [h1, h5, h2]
      linarith [show x + 4 < 0 by linarith [h6]]
    · -- case where y - 4 < 0
      rw [abs_of_neg (show y - 4 < 0 by linarith [show y - 4 < 0 by linarith [show y - 4 < 0 by linarith]])] at h2
      have h5 : y = -x := by linarith
      linarith [h1, h5, h2]
  · -- case where x + 4 < 0
    rw [abs_of_neg (show x + 4 < 0 by linarith [show x + 4 < 0 by linarith [show x + 4 < 0 by linarith]])] at h1
    by_cases h4 : y - 4 ≥ 0
    · -- case where y - 4 ≥ 0
      rw [abs_of_nonneg (show y - 4 ≥ 0 by linarith [h4]) ] at h2
      linarith
    · -- case where y - 4 < 0
      rw [abs_of_neg (show y - 4 < 0 by linarith [show y - 4 < 0 by linarith [show y - 4 < 0 by linarith]])] at h2
      have h5 : x = -6 := by
        nlinarith [h1, h2]
      have h6 : y = 2 := by
        nlinarith [h1, h5]
      simp [Prod.ext_iff]
      exact ⟨by linarith [h5], by linarith [h6]⟩