import Mathlib

theorem algebra_3465 (x : ℝ) (hx : x = 2 * Real.sqrt x + 3) : x = 9 := by
  have h1 : x ≥ 0 := by
    have hsqrt : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
    linarith [hx, hsqrt]
  have h3 : x - 3 = 2 * Real.sqrt x := by
    linarith [hx]
  have h4 : (x - 3) ^ 2 = (2 * Real.sqrt x) ^ 2 := by
    rw [h3]
  have h5 : (x - 3) ^ 2 = x^2 - 6 * x + 9 := by ring
  have h6 : (2 * Real.sqrt x) ^ 2 = 4 * (Real.sqrt x ^ 2) := by ring
  have h7 : Real.sqrt x ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith [h1]
  have h8 : (x - 3) ^ 2 = 4 * x := by
    rw [h4, h6, h7]
  rw [h5] at h8
  have h9 : x ^ 2 - 10 * x + 9 = 0 := by nlinarith [h8]
  have h10 : (x - 1) * (x - 9) = 0 := by
    nlinarith [h9]
  cases' (mul_eq_zero.1 h10) with h11 h12
  · -- Case where x = 1
    have h13 : x = 1 := by linarith [h11]
    rw [h13] at hx
    have h15 : Real.sqrt (1 : ℝ) = 1 := by
      simp [Real.sqrt_eq_iff_sq_eq]
    rw [h15] at hx
    norm_num at hx
  · -- Case where x = 9
    have h16 : x = 9 := by linarith [h12]
    exact h16