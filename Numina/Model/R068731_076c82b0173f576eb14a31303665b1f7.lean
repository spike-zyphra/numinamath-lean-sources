import Mathlib

theorem algebra_197080 (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) :
    5 * a^2 - 6 * a * b + 5 * b^2 > 0 := by 
  rcases h with (ha | hb) 
  · -- Assume a ≠ 0
    have h1 : a ≠ 0 := ha 
    have h2 : 5 * a^2 - 6 * a * b + 5 * b^2 = 5 * (a - 3/5 * b) ^ 2 + 16/5 * b^2 := by 
      nlinarith 
    rw [h2]
    have h3 : 5 * (a - 3/5 * b) ^ 2 ≥ 0 := by 
      nlinarith [sq_nonneg (a - 3/5 * b)]
    have h4 : 16/5 * b^2 ≥ 0 := by 
      nlinarith [sq_nonneg b]
    have h5 : 5 * (a - 3/5 * b) ^ 2 + 16/5 * b^2 > 0 := by 
      by_cases h4' : b = 0 
      · -- if b = 0, then the first term is positive 
        rw [h4']
        have h6 : a ≠ 0 := h1 
        nlinarith [sq_pos_of_ne_zero h6]
      · -- if b ≠ 0, then the second term is positive 
        have h6 : b ≠ 0 := by 
          intro h'
          apply h4'
          linarith 
        nlinarith [sq_nonneg (a - 3/5 * b), sq_pos_of_ne_zero h6]
    linarith
  · -- Assume b ≠ 0
    have h1 : b ≠ 0 := hb 
    have h2 : 5 * a^2 - 6 * a * b + 5 * b^2 = 5 * (a - 3/5 * b) ^ 2 + 16/5 * b^2 := by 
      nlinarith 
    rw [h2]
    have h3 : 16/5 * b^2 > 0 := by 
      have h6 : b ≠ 0 := h1 
      nlinarith [sq_pos_of_ne_zero h6]
    have h4 : 5 * (a - 3/5 * b) ^ 2 ≥ 0 := by 
      nlinarith [sq_nonneg (a - 3/5 * b)]
    linarith