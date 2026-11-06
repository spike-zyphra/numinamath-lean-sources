import Mathlib

/- Let $A=\sqrt{6}+\sqrt{2}$, $B=\sqrt{3}+\sqrt{5}$, then the smaller value between $A$ and $B$ is ___          ___. -/
theorem algebra_2498 {A B : ℝ} (hA : A = Real.sqrt 6 + Real.sqrt 2) (hB : B = Real.sqrt 3 + Real.sqrt 5) : min A B = Real.sqrt 6 + Real.sqrt 2 := by
  rw [hA] at *
  rw [hB] at *
  have h1 : Real.sqrt 6 + Real.sqrt 2 ≤ Real.sqrt 3 + Real.sqrt 5 := by
    have h2 : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg 6
    have h3 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have h4 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    have h5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have h6 : (Real.sqrt 6 + Real.sqrt 2) ^ 2 ≤ (Real.sqrt 3 + Real.sqrt 5) ^ 2 := by
      have h7 : (Real.sqrt 6 + Real.sqrt 2) ^ 2 = (Real.sqrt 6) ^ 2 + (Real.sqrt 2) ^ 2 + 2 * (Real.sqrt 6 * Real.sqrt 2) := by ring
      have h8 : (Real.sqrt 3 + Real.sqrt 5) ^ 2 = (Real.sqrt 3) ^ 2 + (Real.sqrt 5) ^ 2 + 2 * (Real.sqrt 3 * Real.sqrt 5) := by ring
      rw [h7, h8]
      have h9 : (Real.sqrt 6) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
      have h10 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      have h11 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h12 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      rw [h9, h10, h11, h12]
      have h13 : Real.sqrt 6 * Real.sqrt 2 = 2 * Real.sqrt 3 := by
        calc
          Real.sqrt 6 * Real.sqrt 2 = Real.sqrt (6 * 2) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 12 := by norm_num
          _ = Real.sqrt (2^2 * 3) := by norm_num
          _ = (2 : ℝ) * Real.sqrt 3 := by
            rw [Real.sqrt_mul (by norm_num)]
            rw [Real.sqrt_sq (by norm_num)]
      have h14 : Real.sqrt 3 * Real.sqrt 5 = Real.sqrt 15 := by
        calc
          Real.sqrt 3 * Real.sqrt 5 = Real.sqrt (3 * 5) := by rw [Real.sqrt_mul (by norm_num)]
          _ = Real.sqrt 15 := by norm_num
      rw [h13, h14]
      nlinarith [Real.sqrt_nonneg 3, Real.sqrt_nonneg 15, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (15 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3 - Real.sqrt 15 / 2)]
    have h7 : (Real.sqrt 6 + Real.sqrt 2) ≥ 0 := by positivity
    have h8 : (Real.sqrt 3 + Real.sqrt 5) ≥ 0 := by positivity
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg 6, Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5]
  apply min_eq_left
  linarith [h1]