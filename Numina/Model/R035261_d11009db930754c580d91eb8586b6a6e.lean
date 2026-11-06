import Mathlib

theorem algebra_129088 (x : ℝ) (hx : 0 ≤ x) :
    4 = Real.sqrt (7 + Real.sqrt (9 + Real.sqrt (4 + x))) ↔ x = 5180 := by
  constructor
  · -- Assume 4 = Real.sqrt (7 + Real.sqrt (9 + Real.sqrt (4 + x)))
    intro h
    have h1 : Real.sqrt (7 + Real.sqrt (9 + Real.sqrt (4 + x))) = 4 := by linarith
    have h2 : 7 + Real.sqrt (9 + Real.sqrt (4 + x)) = 16 := by
      calc
        7 + Real.sqrt (9 + Real.sqrt (4 + x)) = (Real.sqrt (7 + Real.sqrt (9 + Real.sqrt (4 + x))) ) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = 4 ^ 2 := by
          rw [h1]
        _ = (16 : ℝ) := by norm_num
    have h3 : Real.sqrt (9 + Real.sqrt (4 + x)) = 9 := by linarith
    have h4 : 9 + Real.sqrt (4 + x) = 81 := by
      calc
        9 + Real.sqrt (4 + x) = (Real.sqrt (9 + Real.sqrt (4 + x)) ) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (9 : ℝ) ^ 2 := by
          rw [h3]
        _ = (81 : ℝ) := by norm_num
    have h5 : Real.sqrt (4 + x) = 72 := by linarith
    have h6 : 4 + x = (5184 : ℝ) := by
      calc
        4 + x = (Real.sqrt (4 + x)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (72 : ℝ) ^ 2 := by
          rw [h5]
        _ = (5184 : ℝ) := by
          norm_num
    linarith
  · -- Assume x = 5180
    intro h
    rw [h]
    have h1 : Real.sqrt (4 + (5180 : ℝ)) = 72 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (9 + Real.sqrt (4 + (5180 : ℝ))) = 9 := by
      rw [h1]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (7 + Real.sqrt (9 + Real.sqrt (4 + (5180 : ℝ)))) = 4 := by
      rw [h2]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith [h3]