import Mathlib

theorem inequalities_247177 (x y z : ℝ) (h : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z = 4) :
    x ≤ 2 ∧ Real.sqrt (2 - x) ≥ (y + z) / 2 := by
  have h1 : x ≤ 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 2), sq_nonneg (y ^ 2 - 1), sq_nonneg (z ^ 2 - 1), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y * z - 1), sq_nonneg (y * z + 1), sq_nonneg (x - 2), sq_nonneg (y - z), sq_nonneg (y + z), sq_nonneg (x * y * z - 1)]
  have h_nonneg : 2 - x ≥ 0 := by linarith
  have h5 : Real.sqrt (2 - x) ≥ (y + z) / 2 := by
    have h_nonneg2 : Real.sqrt (2 - x) ≥ 0 := by positivity
    have h_nonneg3 : ((y + z) / 2) ^ 2 ≤ 2 - x := by
      nlinarith [sq_nonneg (y^2 - z^2), sq_nonneg (y - z), sq_nonneg (y ^ 2 + z ^ 2 - 2), sq_nonneg (y + z), 
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), sq_nonneg (x - 2), sq_nonneg (y - z), 
          sq_nonneg (y^2 - z^2), sq_nonneg (x * y * z - 1), sq_nonneg (y * z + 1), sq_nonneg (x + 1), sq_nonneg (2 - x)
        ]
    have h6 : (y + z) / 2 ≤ Real.sqrt (2 - x) := by
      have h7 : ( (y + z) / 2 ) ^ 2 ≤ 2 - x := h_nonneg3
      have h8 : ( Real.sqrt (2 - x) ) ^ 2 = 2 - x := by
        rw [Real.sq_sqrt]
        linarith
      have h11 : Real.sqrt (2 - x) ≥ 0 := by positivity
      by_cases h_nonpos : (y + z) / 2 ≥ 0
      · -- If (y + z) / 2 ≥ 0, then we can apply sq_le_sq
        have h9 : ( (y + z) / 2 ) ≤ Real.sqrt (2 - x) := by
          nlinarith [Real.sqrt_nonneg (2 - x), h_nonpos, h7, Real.sq_sqrt (show (0 : ℝ) ≤ 2 - x by linarith)]
        linarith
      · -- Case where (y + z) / 2 < 0. Then clearly Real.sqrt (2 - x) ≥ (y + z) / 2
        have h10 : (y + z) / 2 < 0 := by linarith
        have h11 : Real.sqrt (2 - x) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (2 - x), Real.sq_sqrt (show (0 : ℝ) ≤ 2 - x by linarith), h10]
    linarith
  exact ⟨h1, h5⟩