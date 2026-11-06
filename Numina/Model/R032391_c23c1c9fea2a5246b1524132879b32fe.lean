import Mathlib

theorem algebra_162307 (x y z : ℝ) (hx : 0 ≤ x) (hy : x ≤ y) (hz : y ≤ z)
    (hzz : z ≤ 4) (h : ∃ d, x^2 = d + 2 ∧ y^2 = d + 4 ∧ z^2 = d + 6) :
    |x - y| + |y - z| ≥ 4 - 2 * Real.sqrt 3 := by
  rcases h with ⟨d, h1, h2, h3⟩
  have h4 : 0 ≤ x := hx
  have h5 : x ≤ y := hy
  have h6 : y ≤ z := hz
  have h7 : z ≤ 4 := hzz
  have h8 : x - y ≤ 0 := by linarith
  have h9 : y - z ≤ 0 := by linarith
  have h10 : |x - y| = y - x := by
    rw [abs_of_nonpos (by linarith)]
    all_goals linarith
  have h11 : |y - z| = z - y := by
    rw [abs_of_nonpos (by linarith)]
    all_goals linarith
  have h12 : |x - y| + |y - z| = z - x := by 
    rw [h10, h11]
    all_goals linarith
  have h13 : z ^ 2 = x ^ 2 + 4 := by
    nlinarith
  have h16 : x^2 ≤ 12 := by
    nlinarith [sq_nonneg (z), sq_nonneg (x), h13, h7]
  have h17 : x ≤ 2 * Real.sqrt 3 := by
    have h18 : (2 * Real.sqrt 3) ^ 2 = 12 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    nlinarith [sq_nonneg (x - 2 * Real.sqrt 3), sq_nonneg (2 * Real.sqrt 3 - x), Real.sqrt_nonneg 3, Real.sqrt_nonneg 3, h4, h18]
  have h18 : z - x ≥ 4 - 2 * Real.sqrt 3 := by
    nlinarith [sq_nonneg (z - 4), sq_nonneg (x - 2 * Real.sqrt 3), sq_nonneg (z - x), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (z^2 - x^2), sq_nonneg (z - x), Real.sqrt_nonneg 3, mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3)]
  linarith [h12, h18]