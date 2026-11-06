import Mathlib

theorem algebra_246321 (a : ℕ → ℝ) (r : ℝ) (h₀ : ∀ n, a n = a 0 + r * n)
    (h₁ : a 3 + a 6 + a 9 = 207) (h₂ : a 4 + a 5 + a 6 + a 7 + a 8 + a 9 + a 10 = 553) :
    a 10 = 109 := by
  have h3 : a 3 = a 0 + 3 * r := by
    rw [h₀ 3]
    ring
  have h6 : a 6 = a 0 + 6 * r := by
    rw [h₀ 6]
    ring
  have h9 : a 9 = a 0 + 9 * r := by
    rw [h₀ 9]
    ring
  rw [h3, h6, h9] at h₁
  have eq1 : a 0 + 6 * r = 69 := by
    linarith
  have h4 : a 4 = a 0 + 4 * r := by
    rw [h₀ 4]
    ring
  have h5 : a 5 = a 0 + 5 * r := by
    rw [h₀ 5]
    ring
  have h7 : a 7 = a 0 + 7 * r := by
    rw [h₀ 7]
    ring
  have h8 : a 8 = a 0 + 8 * r := by
    rw [h₀ 8]
    ring
  have h10 : a 10 = a 0 + 10 * r := by
    rw [h₀ 10]
    ring
  rw [h4, h5, h6, h7, h8, h9, h10] at h₂
  have eq2 : 7 * (a 0) + 49 * r = 553 := by
    linarith
  have h_r : r = 10 := by
    nlinarith [eq1, eq2]
  have h_a0 : a 0 = 9 := by
    linarith [eq1, h_r]
  rw [h10]
  rw [h_a0, h_r]
  norm_num