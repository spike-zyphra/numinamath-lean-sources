import Mathlib

theorem algebra_233420 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (Real.sqrt x) = 3 ↔ x = 81 := by
  constructor
  · -- Forward direction: assume sqrt(sqrt(x)) = 3, prove x = 81
    intro h
    have h1 : Real.sqrt x = 9 := by 
      calc
        Real.sqrt x = Real.sqrt (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = 3 ^ 2 := by rw [h]
        _ = (9 : ℝ) := by norm_num
    have h2 : x = 81 := by
      calc
        x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt]; linarith [hx]
        _ = 9 ^ 2 := by rw [h1]
        _ = (81 : ℝ) := by norm_num
    exact h2
  · -- Backward direction: assume x = 81, prove sqrt(sqrt(x)) = 3
    intro h
    rw [h]
    have h3 : Real.sqrt (81 : ℝ) = 9 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt (9 : ℝ) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3, h4]