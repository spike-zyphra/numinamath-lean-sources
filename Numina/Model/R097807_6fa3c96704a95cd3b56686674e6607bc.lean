import Mathlib

theorem algebra_177862 {x : ℝ} (hx : x > 0) (h : Real.sqrt x + 1 / Real.sqrt x = 3) :
    x / (x ^ 2 + 2018 * x + 1) = 1 / 2025 := by
  have h1 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.mpr
    exact hx
  have h2 : Real.sqrt x * (1 / Real.sqrt x) = 1 := by
    field_simp [h1]
  have h3 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = 9 := by
    rw [h]
    norm_num
  have h4 : (Real.sqrt x + 1 / Real.sqrt x) ^ 2 = (Real.sqrt x) ^ 2 + 2 * (Real.sqrt x * (1 / Real.sqrt x)) + (1 / Real.sqrt x) ^ 2 := by
    ring
  rw [h4] at h3
  rw [h2] at h3
  have h5 : (Real.sqrt x) ^ 2 + (1 / Real.sqrt x) ^ 2 = 7 := by
    nlinarith
  have h6 : (Real.sqrt x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h7 : (1 / Real.sqrt x) ^ 2 = 1 / x := by
    field_simp [h6, h1]
    all_goals nlinarith
  rw [h6, h7] at h5
  have h8 : x ^ 2 + 1 = 7 * x := by
    field_simp at h5 ⊢
    nlinarith
    all_goals nlinarith
  have denominator_eq : x ^ 2 + 2018 * x + 1 = 2025 * x := by
    nlinarith [h8]
  have h9 : x ≠ 0 := by linarith
  rw [denominator_eq]
  field_simp [h9]
  all_goals nlinarith