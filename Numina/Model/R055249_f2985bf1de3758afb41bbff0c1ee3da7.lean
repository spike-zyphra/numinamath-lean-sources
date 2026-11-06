import Mathlib

theorem algebra_93112 (x : ℝ) (hx : x ≥ 2) (h : x + Real.sqrt (x - 2) = 4) :
    x = 3 := by
  have h1 : Real.sqrt (x - 2) = 4 - x := by 
    linarith
  have h2 : (Real.sqrt (x - 2)) ^ 2 = (4 - x) ^ 2 := by
    rw [h1]
  have h3 : (Real.sqrt (x - 2)) ^ 2 = x - 2 := by
    apply Real.sq_sqrt
    linarith
  rw [h3] at h2
  have h4 : x ^ 2 - 9 * x + 18 = 0 := by
    nlinarith
  have h5 : (x - 3) * (x - 6) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- x - 3 = 0, so x = 3.
    linarith
  · -- x - 6 = 0, so x = 6.
    have h8 : x = 6 := by linarith
    rw [h8] at h1
    have h9 : Real.sqrt (6 - 2 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    nlinarith [Real.sqrt_nonneg (6 - 2: ℝ), h9]
  all_goals nlinarith [Real.sqrt_nonneg (x - 2 : ℝ)]