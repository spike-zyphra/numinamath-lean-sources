import Mathlib

theorem algebra_310654 (x : ℝ) (hx : 7 ≤ x) : Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5 ↔ x = 11 := by
  constructor
  · -- Assume Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5, prove x = 11
    intro h
    have h1 : 0 ≤ x - 2 := by linarith
    have h2 : 0 ≤ x - 7 := by linarith
    have h3 : Real.sqrt (x - 2) = 5 - Real.sqrt (x - 7) := by linarith [h]
    have h4 : Real.sqrt (x - 2) ^ 2 = (5 - Real.sqrt (x - 7)) ^ 2 := by
      rw [h3]
    have h5 : Real.sqrt (x - 2) ^ 2 = x - 2 := Real.sq_sqrt (by linarith)
    have h6 : Real.sqrt (x - 7) ^ 2 = x - 7 := Real.sq_sqrt (by linarith)
    have h7 : Real.sqrt (x - 7) = 2 := by
      nlinarith [Real.sqrt_nonneg (x - 2), Real.sqrt_nonneg (x - 7),
        Real.sq_sqrt (show 0 ≤ x - 2 by linarith), Real.sq_sqrt (show 0 ≤ x - 7 by linarith)
      ]
    have h8 : x - 7 = 4 := by
      calc
        x - 7 = Real.sqrt (x - 7) ^ 2 := by
          rw [Real.sq_sqrt (by linarith)]
        _ = (2: ℝ) ^ 2 := by
          rw [h7]
        _ = (4: ℝ) := by
          norm_num
    linarith
  · -- Assume x = 11, prove Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5
    intro h8
    rw [h8]
    have h9 : Real.sqrt (11 - 2: ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h10 : Real.sqrt (11 - 7: ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h9, h10]
    all_goals norm_num