import Mathlib

theorem inequalities_32998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : |a - b| < 2) (h2 : |a - c| < 2) (h3 : |b - c| < 2) :
    a + b + c < Real.sqrt (a * b + 1) + Real.sqrt (a * c + 1) + Real.sqrt (b * c + 1) := by
  have h1' : (a - b) ^ 2 < 4 := by
    cases' abs_lt.mp h1 with h11 h12
    nlinarith
  have h2' : (a - c) ^ 2 < 4 := by
    cases' abs_lt.mp h2 with h21 h22
    nlinarith
  have h3' : (b - c) ^ 2 < 4 := by
    cases' abs_lt.mp h3 with h31 h32
    nlinarith
  have hab : Real.sqrt (a * b + 1) > (a + b) / 2 := by
    have h1 : a * b + 1 > ((a + b) / 2) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - b)]
    have h2 : Real.sqrt (a * b + 1) > Real.sqrt (((a + b) / 2) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      · nlinarith
      all_goals linarith
    have h3 : Real.sqrt (((a + b) / 2) ^ 2) = ( (a + b) / 2 ) := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h3]
  have hac : Real.sqrt (a * c + 1) > (a + c) / 2 := by
    have h1 : a * c + 1 > ((a + c) / 2) ^ 2 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (a - c)]
    have h2 : Real.sqrt (a * c + 1) > Real.sqrt (((a + c) / 2) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      · nlinarith
      all_goals linarith
    have h3 : Real.sqrt (((a + c) / 2) ^ 2) = ( (a + c) / 2 ) := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h3]
  have hbc : Real.sqrt (b * c + 1) > (b + c) / 2 := by
    have h1 : b * c + 1 > ((b + c) / 2) ^ 2 := by
      nlinarith [sq_nonneg (b - c), sq_nonneg (b - c)]
    have h2 : Real.sqrt (b * c + 1) > Real.sqrt (((b + c) / 2) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      · nlinarith
      all_goals linarith
    have h3 : Real.sqrt (((b + c) / 2) ^ 2) = ( (b + c) / 2 ) := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h3]
  linarith [hab, hac, hbc]