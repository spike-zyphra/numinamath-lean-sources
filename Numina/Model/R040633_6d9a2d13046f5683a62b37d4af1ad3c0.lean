import Mathlib

theorem inequalities_33571 (x y z : ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z = 4) :
    x ≤ 2 ∧ (y + z) / 2 ≤ Real.sqrt (2 - x) := by 
  have h1 : x ≤ 2 := by 
    nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1),
      sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y - z), sq_nonneg (y + z),
      sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x ^ 2 - z ^ 2),
      sq_nonneg (x - 1), sq_nonneg (x + 1),
      sq_nonneg (y * z), sq_nonneg (x * y), sq_nonneg (x * z)]
  have h2 : (y + z) / 2 ≤ Real.sqrt (2 - x) := by
    have hx2 : x ≤ 2 := by linarith -- This is h1
    have hx3 : 2 - x ≥ 0 := by linarith -- This follows from h1
    by_cases h3 : (y + z) / 2 ≥ 0
    · -- Case 1: (y + z) / 2 ≥ 0
      have h4 : (Real.sqrt (2 - x)) ^ 2 = 2 - x := by 
        rw [Real.sq_sqrt]
        all_goals linarith
      have h5 : ( (y + z) / 2 ) ^ 2 ≤ 2 - x := by
        nlinarith [sq_nonneg (y^2 - z^2), sq_nonneg (y - z), sq_nonneg (y + z), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (y ^ 2 + z ^ 2 - 2), sq_nonneg (y * z -1), sq_nonneg (x + 0), sq_nonneg (x * y +x * z), sq_nonneg (y + z - (2 : ℝ)), sq_nonneg (y - z), sq_nonneg (x -1), sq_nonneg (x +1), h, sq_nonneg (y + z)]
      have h6 : (y + z) / 2 ≤ Real.sqrt (2 - x) := by
        have h7 : Real.sqrt (2 - x) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show 0 ≤ (2 - x : ℝ) by linarith), h5]
      exact h6
    · -- Case 2: (y + z) / 2 < 0
      have h4 : (y + z) / 2 ≤ 0 := by linarith 
      have h5 : Real.sqrt (2 - x) ≥ 0 := by positivity
      linarith [Real.sqrt_nonneg (2 - x), h4, h5]
  constructor 
  · exact h1
  · exact h2