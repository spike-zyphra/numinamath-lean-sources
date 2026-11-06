import Mathlib

theorem algebra_97650 {x y : ℝ} (h₀ : x + y = 4) (h₁ : x * y = -2) :
    x + x^3 / y^2 + y^3 / x^2 + y = 440 := by

  have h2 : x ≠ 0 := by
    by_contra h
    rw [h] at h₁ 
    nlinarith 
  have h3 : y ≠ 0 := by 
    by_contra h
    rw [h] at h₁ 
    nlinarith

  have h4 : x^2 + y^2 = 20 := by 
    have h2p : x^2 + y^2 = (x + y) ^ 2 - 2 * (x * y) := by
      ring
    rw [h2p, h₀, h₁]
    norm_num

  have h5 : x^3 + y^3 = 88 := by 
    have h3p : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
      ring 
    rw [h3p, h₀, h₁]
    norm_num

  have h6 : x^4 + y^4 = 392 := by 
    have h4p : x^4 + y^4 = (x^2 + y^2) ^ 2 - 2 * (x * y) ^ 2 := by 
      ring 
    rw [h4p, h4, h₁]
    norm_num

  have h7 : x^5 + y^5 = 1744 := by 
    have h5p : x^5 + y^5 = (x + y) * (x^4 + y^4) - (x * y) * (x^3 + y^3) := by
      ring 
    rw [h5p, h₀, h6, h₁, h5]
    norm_num

  have h8 : x^2 * y^2 = 4 := by 
    have h1p : x^2 * y^2 = (x * y) ^ 2 := by 
      ring 
    rw [h1p, h₁]
    norm_num

  have h9 : x^3 / y^2 + y^3 / x^2 = 436 := by 
    field_simp [h2, h3]
    nlinarith [h7, h8]

  linarith [h₀, h9]