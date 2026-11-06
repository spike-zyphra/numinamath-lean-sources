import Mathlib

theorem algebra_3364 {f : ℝ → ℝ} {c : ℝ} (hf : f = fun a => ((2 * c + 1) ^ 2 * (2 * a - 1) / (8 * c ^ 3 + 1) + (6 * c - 12 * a * c) / (8 * c ^ 3 + 1))) (h : f 2019 = 1) : c = 2018 := by 
  have eq1 : f 2019 = ((2 * c + 1) ^ 2 * (2 * 2019 - 1) / (8 * c ^ 3 + 1) + (6 * c - 12 * 2019 * c) / (8 * c ^ 3 + 1)) := by 
    rw [hf]
  rw [eq1] at h
  have eq2 : ((2 * c + 1) ^ 2 * (2 * 2019 - 1) / (8 * c ^ 3 + 1) + (6 * c - 12 * 2019 * c) / (8 * c ^ 3 + 1)) = ((2 * c + 1) ^ 2 * (2 * 2019 - 1) + (6 * c - 12 * 2019 * c)) / (8 * c ^ 3 + 1) := by
    have h1 : (8 * c ^ 3 + 1) ≠ 0 := by
      by_contra h1
      have eq3 : ((2 * c + 1) ^ 2 * (2 * 2019 - 1) / (8 * c ^ 3 + 1) + (6 * c - 12 * 2019 * c) / (8 * c ^ 3 + 1)) = 0 := by
        rw [h1]
        norm_num
      linarith
    field_simp [h1]
    <;> ring
  rw [eq2] at h
  by_cases h1 : (8 * c ^ 3 + 1) = 0
  · -- Denominator is 0
    have eq3 : ((2 * c + 1) ^ 2 * (2 * 2019 - 1) + (6 * c - 12 * 2019 * c)) / (8 * c ^ 3 + 1) = 0 := by
      rw [h1]
      norm_num
    linarith
  · -- Denominator is not 0
    have eq4 : (2 * c + 1) ^ 2 * (2 * 2019 - 1) + (6 * c - 12 * 2019 * c) = (8 * c ^ 3 + 1) := by
      field_simp [show (8 * c ^ 3 + 1) ≠ 0 by assumption] at h ⊢
      nlinarith
    have eq5 : (2 * c + 1) ^ 2 * (2 * 2019 - 1) + (6 * c - 12 * 2019 * c) - (8 * c ^ 3 + 1) = 0 := by linarith
    have h2 : (c - 2018) * (8 * c ^ 2 - 8 * 2018 * c + 4) = 0 := by 
      nlinarith [sq_nonneg (c - 2018), sq_nonneg (c - 2 / 2018), sq_nonneg (c + 2 / 2018), sq_nonneg (c * 2018 - 1), sq_nonneg (c * 2018 + 1)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- c - 2018 = 0
      linarith
    · -- 8 * c ^ 2 - 8 * 2018 * c + 4 = 0
      nlinarith [sq_nonneg (c - 2018), sq_nonneg (c - 2 / 2018), sq_nonneg (c + 2 / 2018), sq_nonneg (c * 2018 - 1), sq_nonneg (c * 2018 + 1)]