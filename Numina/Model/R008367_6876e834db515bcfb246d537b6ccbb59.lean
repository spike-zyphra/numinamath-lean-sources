import Mathlib

theorem algebra_8996 {m n : ℝ} (h : m * 3 + n * 2 = 36 ∧ n * 3 + m * 2 = 9) :
    (m - n) ^ ((1 : ℝ) / 3) = 3 := by
  have h₁ : m * 3 + n * 2 = 36 := h.1
  have h₂ : n * 3 + m * 2 = 9 := by linarith [h.2]
  have hm : m = 18 := by
    linarith
  have hn : n = -9 := by
    linarith [h₂, hm]
  have hmn : m - n = 27 := by
    rw [hm, hn]
    norm_num
  rw [hmn]
  have h1 : (27 : ℝ) ^ ((1 : ℝ) / 3) = 3 := by
    have h2 : (27 : ℝ) = 3 ^ (3 : ℝ) := by norm_num
    rw [h2]
    rw [← Real.rpow_mul]
    norm_num
    all_goals norm_num
  exact h1