import Mathlib

theorem algebra_1519 (x : ℝ) (hx : 0 ≤ 5 * x + 16) (h : x + Real.sqrt (5 * x + 16) = 10) :
    Real.sqrt (5 * x + 16) = 6 := by
  have h1 : Real.sqrt (5 * x + 16) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : x = 10 - Real.sqrt (5 * x + 16) := by
    linarith
  have hb : Real.sqrt (5 * x + 16) = 10 - x := by
    linarith  
  have h0 : (Real.sqrt (5 * x + 16)) ^ 2 = 5 * x + 16 := by
    rw [Real.sq_sqrt]
    all_goals nlinarith
  
  have h1' : (10 - x) ^ 2 = 5 * x + 16 := by
    rw [hb] at h0
    nlinarith
  
  have h2' : x ^ 2 - 25 * x + 84 = 0 := by
    nlinarith

  have h3' : (x - 4) * (x - 21) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h3') with h4 h5
  · -- Case x = 4
    have hx4 : x = 4 := by linarith
    have h6 : Real.sqrt (5 * x + 16) = 6 := by
      rw [hx4]
      have : Real.sqrt (5 * (4 : ℝ) + 16) = 6 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    linarith

  · -- Case x = 21
    have hx21 : x = 21 := by linarith
    exfalso
    rw [hb, hx21] at h
    have h6 : Real.sqrt (5 * (21 : ℝ) + 16) = -11 := by
      nlinarith
    have h7 : Real.sqrt (5 * (21 : ℝ) + 16) ≥ 0 := by
      apply Real.sqrt_nonneg
    nlinarith