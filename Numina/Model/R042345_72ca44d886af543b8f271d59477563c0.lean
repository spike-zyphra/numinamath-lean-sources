import Mathlib
theorem algebra_605149 (x y z : ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z = 4) :
    x ≤ 2 ∧ √(2 - x) ≥ (y + z) / 2 := by
  constructor
  · -- First part: prove that 2 ≤ x
    nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1), sq_nonneg (y - z), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (y + z), sq_nonneg (x - 1), sq_nonneg (y - z), sq_nonneg (y + z - 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
  · -- Second part: √(2 - x) ≥ (y + z) / 2
    have h1 : x ≤ 2 := by 
      nlinarith [sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1), sq_nonneg (y - z), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (y + z), sq_nonneg (x - 1), sq_nonneg (y - z), sq_nonneg (y + z - 2), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
    have h2 : 2 - x ≥ 0 := by linarith
    by_cases h4 : (y + z) / 2 ≥ 0
    · -- Case where (y + z) / 2 ≥ 0 
      have h5 : √(2 - x) ≥ (y + z) / 2 := by 
        have h6 : (√(2 - x)) ^ 2 ≥ ((y + z) / 2) ^ 2 := by 
          have h7 : (√(2 - x)) ^ 2 = 2 - x := by 
            rw [Real.sq_sqrt] 
            linarith 
          nlinarith [sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1), sq_nonneg (y - z), sq_nonneg (x ^ 2 - 1), sq_nonneg (y + z), sq_nonneg (x - 1), sq_nonneg (y - z), sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - z ^ 2), sq_nonneg (y * z), h, mul_nonneg (show (0 : ℝ) ≤ 2 - x by linarith) (show (0 : ℝ) ≤ 2 - x by linarith)]
        have h8 : √(2 - x) ≥ 0 := by 
          apply Real.sqrt_nonneg 
        have h9 : (y + z) / 2 ≥ 0 := h4 
        nlinarith [Real.sqrt_nonneg (2 - x), h9] 
      linarith 
    · -- Case where (y + z) / 2 < 0 
      have h4' : (y + z) / 2 < 0 := by linarith 
      have h5 : √(2 - x) ≥ (y + z) / 2 := by 
        have h7 : √(2 - x) ≥ 0 := Real.sqrt_nonneg (2 - x) 
        nlinarith 
      linarith