import Mathlib

theorem algebra_276386 {x y : ℝ} (h₀ : x + y = 4) (h₁ : x * y = -2) :
    x + x ^ 3 / y ^ 2 + y ^ 3 / x ^ 2 + y = 440 := by

  have h2 : y ≠ 0 := by
    by_contra h
    have h3 : y = 0 := by linarith
    rw [h3] at h₁ 
    have h4 : x * 0 = -2 := by linarith
    have h5 : x * 0 = 0 := by 
      ring
    linarith -- contradiction

  have h3 : x ≠ 0 := by
    by_contra h
    have h4 : x = 0 := by linarith
    rw [h4] at h₁ 
    have h5 : 0 * y = -2 := by linarith
    have h6 : 0 * y = 0 := by 
      ring
    linarith -- contradiction
  
  have h4 : x ^ 2 + y ^ 2 = 20 := by 
    nlinarith 

  have h5 : x ^ 3 + y ^ 3 = 88 := by
    nlinarith [h₀, h₁, h4]

  have h6 : x ^ 4 + y ^ 4 = 392 := by 
    nlinarith [h₀, h₁, h4, h5]

  have h7 : x ^ 5 + y ^ 5 = 1744 := by 
    nlinarith [h₀, h₁, h4, h5, h6]

  have h8 : x ^ 3 / y ^ 2 + y ^ 3 / x ^ 2 = (x ^ 5 + y ^ 5) / ((x * y) ^ 2) := by 
    field_simp [h2, h3]
    ring

  have h9 : (x ^5 + y ^ 5 : ℝ) = 1744 := by
    linarith

  have h10 : (x * y : ℝ) ^ 2 = 4 := by 
    nlinarith

  have h11 : (x ^5 + y ^ 5 : ℝ) / ((x * y) ^ 2) = 436 := by 
    rw [h9, h10]
    norm_num

  have h12 : x + y = 4 := h₀

  linarith [h12, h8, h11]