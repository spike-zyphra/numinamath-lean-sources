import Mathlib

theorem inequalities_170317 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a + b + c ≥ Real.sqrt ((a + 2) * (b + 2) * (c + 2) / 3) := by
  have h1 : (a + b + c) ^ 2 ≥ (a + 2) * (b + 2) * (c + 2) / 3 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
        sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        habc, mul_pos (show 0 < a * b by nlinarith) (show 0 < c by nlinarith)]
  have h2 : Real.sqrt ((a + b + c) ^ 2) ≥ Real.sqrt ((a + 2) * (b + 2) * (c + 2) / 3) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (a + b + c), h1]
  have h3 : Real.sqrt ((a + b + c) ^ 2) = a + b + c := by
    rw [Real.sqrt_sq (show 0 ≤ (a + b + c : ℝ) by positivity)]
  rw [h3] at h2
  linarith