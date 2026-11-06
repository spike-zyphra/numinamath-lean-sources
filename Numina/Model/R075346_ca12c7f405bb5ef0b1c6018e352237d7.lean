import Mathlib

theorem algebra_100354 {a b : ℝ} (h₀ : a = -b) (h₁ : abs (a - b) = 2) :
    (a^2 + 2 * a * b + 2 * b^2 + 2 * a + 2 * b + 1) / (a^2 + 3 * a * b + b^2 + 3) = 1 := by
  have h2 : a - b = -2 * b := by
    rw [show a = -b by linarith [h₀]]
    linarith
  rw [h2] at h₁
  have h3 : abs (-2 * b : ℝ) = abs (-2 : ℝ) * abs (b : ℝ) := by
    rw [abs_mul]
  rw [h3] at h₁
  have h4 : abs (-2 : ℝ) = (2 : ℝ) := by norm_num
  rw [h4] at h₁
  have h5 : abs (b : ℝ) = 1 := by
    linarith
  cases' eq_or_eq_neg_of_abs_eq h5 with h6 h7
  · -- Case where b = 1
    have ha1 : a = -1 := by
      rw [show b = 1 by linarith [h6] ] at h₀
      linarith
    have hb1 : b = 1 := by linarith [h6]
    rw [ha1, hb1]
    norm_num
  · -- Case where b = -1
    have ha2 : a = 1 := by
      rw [show b = -1 by linarith [h7] ] at h₀
      linarith
    have hb2 : b = -1 := by linarith [h7]
    rw [ha2, hb2]
    norm_num