import Mathlib

theorem algebra_14851 (x : ℝ) (hx : x ≥ -3) :
    x ^ 2 + 4 * x + 4 * x * Real.sqrt (x + 3) = 13 ↔ x = 1 := by 
  constructor
  · -- Forward direction: Given the equation, prove x = 1
    intro h
    have h1 : Real.sqrt (x + 3) ≥ 0 := by positivity
    have h2 : (Real.sqrt (x + 3)) ^ 2 = x + 3 := by 
      rw [Real.sq_sqrt]
      linarith
    have h3 : 4 * x * Real.sqrt (x + 3) = 13 - x^2 - 4 * x := by 
      nlinarith [h, h1]
    have h4 : (4 * x * Real.sqrt (x + 3)) ^ 2 = (13 - x^2 - 4 * x) ^ 2 := by
      rw [h3]
    have h5 : (4 * x * Real.sqrt (x + 3)) ^ 2 = 16 * x^2 * (x + 3) := by
      calc
        (4 * x * Real.sqrt (x + 3)) ^ 2 = 16 * x ^ 2 * (Real.sqrt (x + 3) ^ 2) := by
          ring_nf
          <;> nlinarith
        _ = 16 * x ^ 2 * (x + 3) := by 
          rw [h2]
        _ = 16 * x^2 * (x + 3) := by ring
    rw [h5] at h4
    -- Expanding right side square (x^2 +4x -13)^2
    rw [show (13 - x^2 - 4 * x) ^ 2 = (x ^ 2 + 4 * x - 13) ^ 2 by ring] at h4
    -- Factorize polynomial and find roots
    have h9 : (x - 1) * (x - 13) * (x ^2 + 6 * x + 13) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 + 4 * x - 13), sq_nonneg (x + 3), sq_nonneg (Real.sqrt (x + 3) ^ 2 - (x + 3)), sq_nonneg (x * (Real.sqrt (x + 3))), sq_nonneg ((x - 1) * (Real.sqrt (x + 3))), sq_nonneg ((x - 13) * (Real.sqrt (x + 3)))]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · cases' (mul_eq_zero.mp h10) with h12 h13
      · -- First case: (x - 1) = 0
        linarith
      · -- Second case: (x - 13) = 0
        have h14 : x = 13 := by linarith
        rw [h14] at h
        nlinarith [Real.sqrt_nonneg (13 + 3), Real.sq_sqrt (show (0 : ℝ) ≤ (13 + 3 : ℝ) by norm_num)]
    · -- Third case: (x ^2 + 6 * x + 13) = 0
      have h15 : x ^2 + 6 * x + 13 = 0 := by 
        nlinarith [h11]
      have h16 : (x + 3) ^ 2 = -4 := by 
        nlinarith [sq_nonneg (x + 3), sq_nonneg (Real.sqrt (x + 3))]
      nlinarith [sq_nonneg (x + 3), sq_nonneg (Real.sqrt (x + 3)), h16]
  · -- Backward direction: If x = 1, prove the equation
    intro h
    rw [h]
    have h3 : Real.sqrt (1 + 3) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h3]
    nlinarith