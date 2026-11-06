import Mathlib

theorem algebra_9643 : round ((3 + Real.sqrt 13)^3) = 288 := by
  have h1 : (3 + Real.sqrt 13) ^ 3 = 144 + 40 * Real.sqrt 13 := by
    ring_nf
    have h2 : Real.sqrt 13 ^ 2 = 13 := by
      rw [Real.sq_sqrt]
      norm_num
    have h3 : Real.sqrt 13 ^ 3 = Real.sqrt 13 * 13 := by
      calc
        Real.sqrt 13 ^ 3 = Real.sqrt 13 ^ 2 * Real.sqrt 13 := by ring
        _ = 13 * Real.sqrt 13 := by rw [h2]
        _ = Real.sqrt 13 * 13 := by ring
    rw [h3]
    nlinarith
  rw [h1]
  have h4 : 3.604 < Real.sqrt 13 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  have h5 : Real.sqrt 13 < 3.606 := by
    nlinarith [Real.sqrt_nonneg 13, Real.sq_sqrt (show (0 : ℝ) ≤ (13 : ℝ) by norm_num)]
  have h6 : 144 + 40 * Real.sqrt 13 > 288.16 := by
    nlinarith [h4]
  have h7 : 144 + 40 * Real.sqrt 13 < 288.24 := by
    nlinarith [h5]
  rw [round_eq]
  simp only [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try nlinarith)