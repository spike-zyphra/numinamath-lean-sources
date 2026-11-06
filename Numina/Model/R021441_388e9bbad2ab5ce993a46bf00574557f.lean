import Mathlib

theorem algebra_10429
    (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (habc : a * b * c = 10 ^ 11)
    (h : Real.logb 10 a * Real.logb 10 (b * c) + Real.logb 10 b * Real.logb 10 (c * a) + Real.logb 10 c * Real.logb 10 (a * b) = 40) :
    Real.sqrt (Real.logb 10 a ^ 2 + Real.logb 10 b ^ 2 + Real.logb 10 c ^ 2) = 9 := by
  have h1 : Real.logb 10 a + Real.logb 10 b + Real.logb 10 c = 11 := by
    have h2 : Real.logb 10 (a * b * c) = 11 := by
      calc
        Real.logb 10 (a * b * c) = Real.logb 10 (10 ^ 11) := by rw [habc]
        _ = 11 := by
          simp [Real.logb_pow]
    have h3 : Real.logb 10 (a * b * c) = Real.logb 10 a + Real.logb 10 b + Real.logb 10 c := by
      simp [Real.logb_mul, ha.ne.symm, hb.ne.symm, hc.ne.symm]
    linarith [h2, h3]
  have h2 : Real.logb 10 (b * c) = Real.logb 10 b + Real.logb 10 c := by
    rw [Real.logb_mul (by positivity) (by positivity)]
  have h3 : Real.logb 10 (c * a) = Real.logb 10 c + Real.logb 10 a := by
    rw [Real.logb_mul (by positivity) (by positivity)]
  have h4 : Real.logb 10 (a * b) = Real.logb 10 a + Real.logb 10 b := by
    rw [Real.logb_mul (by positivity) (by positivity)]
  have heq : Real.logb 10 a * (Real.logb 10 b + Real.logb 10 c) + Real.logb 10 b * (Real.logb 10 c + Real.logb 10 a) + Real.logb 10 c * (Real.logb 10 a + Real.logb 10 b) = 40 := by
    rw [h2, h3, h4] at h
    linarith
  have h6 : Real.logb 10 a * Real.logb 10 b + Real.logb 10 b * Real.logb 10 c + Real.logb 10 a * Real.logb 10 c = 20 := by
    have h5 : Real.logb 10 a * (Real.logb 10 b + Real.logb 10 c) + Real.logb 10 b * (Real.logb 10 c + Real.logb 10 a) + Real.logb 10 c * (Real.logb 10 a + Real.logb 10 b) = 2 * (Real.logb 10 a * Real.logb 10 b + Real.logb 10 b * Real.logb 10 c + Real.logb 10 a * Real.logb 10 c) := by
      ring
    linarith [heq, h5]
  have h7 : Real.logb 10 a ^ 2 + Real.logb 10 b ^ 2 + Real.logb 10 c ^ 2 = 81 := by
    have h8 : Real.logb 10 a ^ 2 + Real.logb 10 b ^ 2 + Real.logb 10 c ^ 2 = (Real.logb 10 a + Real.logb 10 b + Real.logb 10 c) ^ 2 - 2 * (Real.logb 10 a * Real.logb 10 b + Real.logb 10 b * Real.logb 10 c + Real.logb 10 a * Real.logb 10 c) := by
      ring
    rw [h8, h1, h6]
    all_goals norm_num
  rw [h7]
  exact Real.sqrt_eq_cases.2 (by norm_num)