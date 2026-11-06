import Mathlib

theorem algebra_93145 {m n b : ℝ} (h₀ : 0 < m) (h₁ : 0 < n) (h₂ : Real.logb 10 m = b - Real.logb 10 n) :
    m = 10 ^ b / n := by
  have h3 : Real.logb 10 m + Real.logb 10 n = b := by
    linarith
  have h4 : Real.logb 10 m + Real.logb 10 n = Real.logb 10 (m * n) := by
    rw [Real.logb_mul (by linarith) (by linarith)]
  have h5 : Real.logb 10 (m * n) = b := by
    linarith [h3, h4]
  have h6 : m * n = (10 : ℝ) ^ b := by
    have h7 : m * n > 0 := by
      positivity
    have h8 : Real.logb 10 (m * n) = b := h5
    rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by positivity) ] at h8
    · -- First case: m * n = 10 ^ b
      linarith
    all_goals linarith
  have h7 : m = (10 ^ b) / n := by
    have h8 : m * n = 10 ^ b := by
      simpa using h6
    have h9 : n ≠ 0 := by linarith
    field_simp [h9]
    linarith
  linarith [h7]