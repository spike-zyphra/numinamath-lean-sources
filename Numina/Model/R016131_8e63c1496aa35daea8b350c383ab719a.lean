import Mathlib

theorem algebra_317848 {x y : ℝ} (h₀ : x - y = 1) (h₁ : x ^ 3 - y ^ 3 = 2) :
    x ^ 4 + y ^ 4 = 23 / 9 ∧ x ^ 5 - y ^ 5 = 29 / 9 := by
  have h2 : x ^ 2 + x * y + y ^ 2 = 2 := by
    have h3 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by 
      ring
    rw [h3] at h₁
    rw [h₀] at h₁
    linarith
  have h3 : x * y = 1 / 3 := by
    have h4 : x ^ 2 + y ^ 2 = (x - y) ^ 2 + 2 * (x * y) := by
      nlinarith 
    rw [h₀] at h4
    have h5 : x ^ 2 + y ^ 2 + (x * y) = 2 := by
      nlinarith [h4, h2]
    nlinarith
  have h4 : x ^ 4 + y ^ 4 = 23 / 9 := by
    have h7 : x ^ 2 + y ^ 2 = 5 / 3 := by
      nlinarith
    have h8 : x ^ 4 + y ^ 4 = (x ^ 2 + y ^ 2) ^ 2 - 2 * (x * y) ^ 2 := by
      ring
    rw [h8, h7, h3]
    norm_num
  have h5' : x ^ 5 - y ^ 5 = 29 / 9 := by 
    have h8 : x ^ 5 - y ^ 5 = (x - y) * (x ^ 4 + x ^ 3 * y + x ^ 2 * y ^ 2 + x * y ^ 3 + y ^ 4) := by 
      ring
    rw [h8, h₀]
    have h9 : x ^ 3 * y + x * y ^ 3 = 5 / 9 := by
      have h11 : x ^ 3 * y + x * y ^ 3 = (x * y) * (x ^ 2 + y ^ 2) := by
        ring
      have h12 : x ^ 2 + y ^ 2 = 5 / 3 := by 
        nlinarith
      rw [h11, h3, h12]
      norm_num
    have h12 : x ^ 2 * y ^ 2 = 1 / 9 := by
      calc
        x ^ 2 * y ^ 2 = (x * y) ^ 2 := by ring
        _ = (1 / 3) ^ 2 := by rw [h3]
        _ = 1 / 9 := by norm_num
    nlinarith [h4, h9, h12]
  constructor
  · exact h4
  · exact h5'