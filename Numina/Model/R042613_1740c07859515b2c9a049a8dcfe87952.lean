import Mathlib

theorem algebra_5575
  (a b c : ℝ)
  (ha : a ≥ 0)
  (hb : b ≥ 1)
  (hc : c ≥ -1)
  (h : a + 4 * b + c + 3 = 2 * √a + 4 * √(b - 1) + 4 * √(c + 1)) :
  a + b + c = 5.25 := by

  have h1 : (√a) ^ 2 = a := by
    rw [Real.sq_sqrt]
    linarith
  have h2 : (√(b - 1)) ^ 2 = b - 1 := by
    rw [Real.sq_sqrt]
    linarith
  have h3 : (√(c + 1)) ^ 2 = c + 1 := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : (Real.sqrt a - 1) ^ 2 + 4 * (Real.sqrt (b - 1) - 0.5) ^ 2 + (Real.sqrt (c + 1) - 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt (b - 1) - 0.5), sq_nonneg (Real.sqrt (c + 1) - 2),
      Real.sqrt_nonneg a, Real.sqrt_nonneg (b - 1), Real.sqrt_nonneg (c + 1), 
      h1, h2, h3, h, 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (b - 1)), 
      mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (c + 1)), 
      mul_nonneg (Real.sqrt_nonneg (b - 1)) (Real.sqrt_nonneg (c + 1))]
  have h5 : Real.sqrt a - 1 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt (b - 1) - 0.5), sq_nonneg (Real.sqrt (c + 1) - 2),
      Real.sqrt_nonneg a, Real.sqrt_nonneg (b - 1), Real.sqrt_nonneg (c + 1)]
  have h6 : Real.sqrt (b - 1) - 0.5 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt (b - 1) - 0.5), sq_nonneg (Real.sqrt (c + 1) - 2),
      Real.sqrt_nonneg a, Real.sqrt_nonneg (b - 1), Real.sqrt_nonneg (c + 1)]
  have h7 : Real.sqrt (c + 1) - 2 = 0 := by
    nlinarith [sq_nonneg (Real.sqrt a - 1), sq_nonneg (Real.sqrt (b - 1) - 0.5), sq_nonneg (Real.sqrt (c + 1) - 2),
      Real.sqrt_nonneg a, Real.sqrt_nonneg (b - 1), Real.sqrt_nonneg (c + 1)]
  have ha' : a = 1 := by
    have h8 : Real.sqrt a = 1 := by
      nlinarith [h5, Real.sqrt_nonneg a]
    have h9 : Real.sqrt a ≥ 0 := Real.sqrt_nonneg a
    calc
      a = (Real.sqrt a) ^ 2 := by
        rw [Real.sq_sqrt]
        all_goals linarith
      _ = (1) ^ 2 := by 
        rw [h8]
      _ = (1 : ℝ) := by norm_num
  have hb'' : b = 1.25 := by
    have h8 : Real.sqrt (b - 1) = 0.5 := by
      nlinarith [h6, Real.sqrt_nonneg (b - 1)]
    have h9 : Real.sqrt (b - 1) ≥ 0 := Real.sqrt_nonneg (b - 1)
    have hb' : b - 1 = (0.5 : ℝ) ^ 2 := by
      calc
        b - 1 = (Real.sqrt (b - 1)) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (0.5) ^ 2 := by 
          rw [h8]
          all_goals nlinarith
    nlinarith
  have hc'' : c = 3 := by
    have h9 : Real.sqrt (c + 1) = 2 := by
      nlinarith [h7, Real.sqrt_nonneg (c + 1)]
    have hc' : c + 1 = 4 := by 
      calc
        c + 1 = (Real.sqrt (c + 1)) ^ 2 := by 
          rw [Real.sq_sqrt]
          linarith
        _ = (2 : ℝ) ^ 2 := by 
          rw [h9]
          all_goals nlinarith
        _ = (4 : ℝ) := by norm_num
    linarith 
  rw [ha', hb'', hc'']
  all_goals norm_num