import Mathlib

theorem algebra_285212 {f : ℝ → ℝ} (h : ∀ x ≠ 0, f (x + 1 / x) = x ^ 6 + 1 / x ^ 6) :
    f 3 = 322 := by
  have h1 : ∀ x ≠ 0, x + 1 / x = 3 → f 3 = x ^ 6 + 1 / x ^ 6 := by
    intro x hx h_eq
    have h2 : f (x + 1 / x) = x ^ 6 + 1 / x ^ 6 := h x hx
    rw [h_eq] at h2
    linarith
  have hx0 : ((3 + Real.sqrt 5) / 2 : ℝ) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have hx1 : ((3 + Real.sqrt 5) / 2 : ℝ) + 1 / ((3 + Real.sqrt 5) / 2) = 3 := by
    field_simp [(show ((3 + Real.sqrt 5) / 2 : ℝ) ≠ 0 by assumption)]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have eq1 : f 3 = ((3 + Real.sqrt 5) / 2) ^ 6 + 1 / ((3 + Real.sqrt 5) / 2) ^ 6 := by
    apply h1 ((3 + Real.sqrt 5) / 2) hx0 hx1
  rw [eq1]
  have hx2 : ((3 + Real.sqrt 5) / 2 : ℝ) + 1 / ((3 + Real.sqrt 5) / 2 : ℝ) = 3 := hx1
  have hx4 : ((3 + Real.sqrt 5) / 2 : ℝ) ^ 3 + 1 / ((3 + Real.sqrt 5) / 2 : ℝ) ^ 3 = 18 := by
    have h18 : ((3 + Real.sqrt 5) / 2 : ℝ) ^ 3 + 1 / ((3 + Real.sqrt 5) / 2 : ℝ) ^ 3 = (((3 + Real.sqrt 5) / 2 + 1 / ((3 + Real.sqrt 5) / 2)) ^ 3 - 3 * ((3 + Real.sqrt 5) / 2 + 1 / ((3 + Real.sqrt 5) / 2))) := by
      field_simp [(show ((3 + Real.sqrt 5) / 2 : ℝ) ≠ 0 by assumption)]
      <;> ring
    rw [h18, hx1]
    norm_num
  have hx5 : ((3 + Real.sqrt 5) / 2 : ℝ) ^ 6 + 1 / ((3 + Real.sqrt 5) / 2 : ℝ) ^ 6 = 322 := by
    calc
      ((3 + Real.sqrt 5) / 2 : ℝ) ^ 6 + 1 / ((3 + Real.sqrt 5) / 2 : ℝ) ^ 6 
          = ((( (3 + Real.sqrt 5) / 2 : ℝ) ^ 3 + 1 / ((3 + Real.sqrt 5) / 2 : ℝ) ^ 3 ) )^2 - 2 := by
            field_simp [(show ((3 + Real.sqrt 5) / 2 : ℝ) ≠ 0 by assumption)]
            <;> ring
      _ = (18)^2 - 2 := by 
        rw [hx4]
      _ = (324 : ℝ) - 2 := by norm_num
      _ = (322 : ℝ) := by norm_num
  linarith [hx5]