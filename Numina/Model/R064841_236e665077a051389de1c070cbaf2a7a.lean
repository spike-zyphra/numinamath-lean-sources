import Mathlib

theorem algebra_311679 {x y : ℝ} (h₀ : x + y = 1) (h₁ : x ^ 2 + y ^ 2 = 2) :
    x ^ 7 + y ^ 7 = 71 / 8 := by
  have h2 : x * y = -1 / 2 := by
    have h3 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
      nlinarith
    rw [h₀] at h3
    nlinarith
  have h3 : x ^ 3 + y ^ 3 = 5 / 2 := by
    have h6 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
      ring_nf
    rw [h6, h₀, h2]
    norm_num
  have h4 : x ^ 4 + y ^ 4 = 7 / 2 := by
    have h6 : x ^ 4 + y ^ 4 = (x + y) * (x ^ 3 + y ^ 3) - (x * y) * (x ^ 2 + y ^ 2) := by
      ring_nf
    rw [h6, h₀, h3, h₁, h2]
    norm_num
  have h5 : x ^ 5 + y ^ 5 = 19 / 4 := by
    have h6 : x ^ 5 + y ^ 5 = (x + y) * (x ^ 4 + y ^ 4) - (x * y) * (x ^ 3 + y ^ 3) := by
      ring_nf
    rw [h6, h₀, h4, h3, h2]
    norm_num
  have h6 : x ^ 6 + y ^ 6 = 13 / 2 := by
    have h7 : x ^ 6 + y ^ 6 = (x + y) * (x ^ 5 + y ^ 5) - (x * y) * (x ^ 4 + y ^ 4) := by
      ring_nf
    rw [h7, h₀, h5, h4, h2]
    norm_num
  have h7 : x ^ 7 + y ^ 7 = 71 / 8 := by
    have h8 : x ^ 7 + y ^ 7 = (x + y) * (x ^ 6 + y ^ 6) - (x * y) * (x ^ 5 + y ^ 5) := by
      ring_nf
    rw [h8, h₀, h6, h5, h2]
    norm_num
  linarith