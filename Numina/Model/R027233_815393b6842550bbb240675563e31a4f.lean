import Mathlib

theorem algebra_184163 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 10 ^ 11) (h : Real.logb 10 a * Real.logb 10 (b * c) +
    Real.logb 10 b * Real.logb 10 (c * a) + Real.logb 10 c * Real.logb 10 (a * b) = 40) :
    Real.sqrt (Real.logb 10 a ^ 2 + Real.logb 10 b ^ 2 + Real.logb 10 c ^ 2) = 9 := by

  have h1 : Real.logb 10 (a * b * c) = 11 := by
    calc
      Real.logb 10 (a * b * c) = Real.logb 10 (10 ^ 11) := by
        rw [show a * b * c = (10 ^ 11 : ℝ) by linarith]
      _ = 11 := by
        simp [Real.logb_pow]

  have h2 : Real.logb 10 (a * b * c) = Real.logb 10 a + Real.logb 10 b + Real.logb 10 c := by
    simp [Real.logb_mul, ha.ne.symm, hb.ne.symm, hc.ne.symm]

  have h3 : Real.logb 10 a + Real.logb 10 b + Real.logb 10 c = 11 := by
    linarith [h1, h2]

  have h4 : Real.logb 10 (b * c) = Real.logb 10 b + Real.logb 10 c := by
    rw [Real.logb_mul (by linarith) (by linarith)]

  have h5 : Real.logb 10 (c * a) = Real.logb 10 c + Real.logb 10 a := by
    rw [Real.logb_mul (by linarith) (by linarith)]

  have h6 : Real.logb 10 (a * b) = Real.logb 10 a + Real.logb 10 b := by
    rw [Real.logb_mul (by linarith) (by linarith)]

  rw [h4, h5, h6] at h

  have h9 : Real.logb 10 a ^ 2 + Real.logb 10 b ^ 2 + Real.logb 10 c ^ 2 = 81 := by
    nlinarith [sq_nonneg (Real.logb 10 a + Real.logb 10 b + Real.logb 10 c - 11), sq_nonneg (Real.logb 10 a - Real.logb 10 b), sq_nonneg (Real.logb 10 a - Real.logb 10 c), sq_nonneg (Real.logb 10 b - Real.logb 10 c)]

  have h10 : Real.sqrt (Real.logb 10 a ^ 2 + Real.logb 10 b ^ 2 + Real.logb 10 c ^ 2) = 9 := by
    rw [h9]
    exact Real.sqrt_eq_cases.2 (by norm_num)

  exact h10