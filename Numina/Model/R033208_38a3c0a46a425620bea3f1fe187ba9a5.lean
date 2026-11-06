import Mathlib

theorem algebra_166000 : ⌈(Real.sqrt 3 + Real.sqrt 2)^6⌉ = 970 := by
  have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h1]
      _ = 9 := by norm_num
  have h4 : Real.sqrt 2 ^ 4 = 4 := by
    calc
      Real.sqrt 2 ^ 4 = (Real.sqrt 2 ^ 2) ^ 2 := by ring
      _ = 2 ^ 2 := by rw [h2]
      _ = 4 := by norm_num
  have h5 : (Real.sqrt 3 + Real.sqrt 2) ^ 2 = 5 + 2 * Real.sqrt 6 := by
    calc
      (Real.sqrt 3 + Real.sqrt 2) ^ 2 = Real.sqrt 3 ^ 2 + Real.sqrt 2 ^ 2 + 2 * (Real.sqrt 3 * Real.sqrt 2) := by ring
      _ = 3 + 2 + 2 * (Real.sqrt 3 * Real.sqrt 2) := by rw [h1, h2]
      _ = 5 + 2 * (Real.sqrt 3 * Real.sqrt 2) := by ring
      _ = 5 + 2 * Real.sqrt 6 := by
        have h9 : Real.sqrt 3 * Real.sqrt 2 = Real.sqrt 6 := by
          rw [← Real.sqrt_mul (by norm_num)]
          all_goals norm_num
        rw [h9]
  have h6 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 = 485 + 198 * Real.sqrt 6 := by
    calc
      (Real.sqrt 3 + Real.sqrt 2) ^ 6 = ((Real.sqrt 3 + Real.sqrt 2) ^ 2) ^ 3 := by ring
      _ = (5 + 2 * Real.sqrt 6) ^ 3 := by rw [h5]
      _ = 485 + 198 * Real.sqrt 6 := by
        ring_nf
        <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h11 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 < 970 := by
    nlinarith [h6, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h12 : (Real.sqrt 3 + Real.sqrt 2) ^ 6 > 969 := by
    nlinarith [h6, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
  have h13 : ⌈(Real.sqrt 3 + Real.sqrt 2) ^ 6⌉ = 970 := by
    rw [Int.ceil_eq_iff]
    constructor <;> (try norm_num) <;> nlinarith
  exact h13