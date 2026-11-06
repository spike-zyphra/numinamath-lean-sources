import Mathlib

open Real

theorem algebra_154188 {x : ℝ} (hx : x ≠ 0) (h : 1 / Real.cos (2022 * x) + Real.tan (2022 * x) = 1 / 2022) :
    1 / Real.cos (2022 * x) - Real.tan (2022 * x) = 2022 := by

  have h1 : Real.cos (2022 * x) ≠ 0 := by
    by_contra h1
    have htan : Real.tan (2022 * x) = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h1]
    have h2 : 1 / Real.cos (2022 * x) = 0 := by
      field_simp [h1]
    rw [htan, h2] at h
    norm_num at h

  have eq1 : (1 / Real.cos (2022 * x) + Real.tan (2022 * x)) * (1 / Real.cos (2022 * x) - Real.tan (2022 * x)) = 1 := by
    have htan : Real.tan (2022 * x) = Real.sin (2022 * x) / Real.cos (2022 * x) := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan]
    have h1' : Real.cos (2022 * x) ≠ 0 := h1
    field_simp [h1']
    <;> nlinarith [Real.sin_sq_add_cos_sq (2022 * x)]

  rw [h] at eq1

  have h2 : (1 / 2022 : ℝ) * (1 / Real.cos (2022 * x) - Real.tan (2022 * x)) = 1 := by
    linarith

  have h3 : (1 / Real.cos (2022 * x) - Real.tan (2022 * x)) = 2022 := by
    linarith
  exact h3