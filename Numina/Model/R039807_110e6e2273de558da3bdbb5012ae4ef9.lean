import Mathlib

theorem algebra_13727 {x : ℝ} (hx : x^3-3*Real.sqrt 2*x^2+6*x-2*Real.sqrt 2-8=0) :
    x^5-41*x^2+2012=1998 := by
  have h1 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h2 : Real.sqrt 2 ^ 3 = (2 : ℝ) * Real.sqrt 2 := by
    calc
      Real.sqrt 2 ^ 3 = (Real.sqrt 2) ^ 2 * Real.sqrt 2 := by ring
      _ = (2 : ℝ) * Real.sqrt 2 := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  have beeq : (x - Real.sqrt 2) ^ 3 = 8 := by 
    nlinarith [h1, h2, sq_nonneg (x * x - 4 * x + 2), sq_nonneg (x - (2 + Real.sqrt 2)), sq_nonneg (Real.sqrt 2 ^ 2 - 2), sq_nonneg (x - 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
  have beeq2 : x = Real.sqrt 2 + 2 := by
    have h1 : Real.sqrt 2 > (0 : ℝ) := by positivity
    have eq1 : (x - Real.sqrt 2) ^ 3 = 8 := beeq
    have eq2 : x - Real.sqrt 2 = 2 := by
      have beeq3 : (x - Real.sqrt 2) ^ 3 - 8 = 0 := by linarith [eq1]
      have beeq4 : (x - Real.sqrt 2) ^ 3 - 8 = (x - Real.sqrt 2 - 2) * ((x - Real.sqrt 2) ^ 2 + (x - Real.sqrt 2) * 2 + 4) := by ring_nf
      rw [beeq4] at beeq3
      cases' (mul_eq_zero.mp beeq3) with h h
      · -- Be the first factor, thus beeq.
        linarith  -- Solving linear
      · -- Case of the quadratic factor.
        have : (x - Real.sqrt 2) ^ 2 + (x - Real.sqrt 2) * 2 + 4 ≠ 0 := by
          intro hc
          have beeq5 : (x - Real.sqrt 2) ^ 2 + (x - Real.sqrt 2) * 2 + 4 > 0 := by
            nlinarith [sq_nonneg ((x - Real.sqrt 2) + 1)]
          linarith
        tauto
    nlinarith
  have eq1 : x^2 = 4 * x - 2 := by
    rw [show Real.sqrt 2 = x - 2 by linarith [beeq2]] at h1
    nlinarith
  have eq2 : x^3 = 14 * x - 8 := by
    calc 
      x^3 = x * x^2 := by ring
      _ = x * (4 * x - 2) := by rw [eq1]
      _ = 4 * x^2 - 2 * x := by nlinarith
      _ = 4 * (4 * x - 2) - 2 * x := by rw [eq1]
      _ = 14 * x - 8 := by nlinarith
  have eq3 : x^4 = 48 * x - 28 := by
    calc
      x^4 = x * x^3 := by ring
      _ = x * (14 * x - 8) := by rw [eq2]
      _ = 14 * x^2 - 8 * x := by nlinarith
      _ = 14 * (4 * x - 2) - 8 * x := by rw [eq1]
      _ = 48 * x - 28 := by nlinarith
  have eq4 : x^5 = 164 * x - 96 := by
    calc 
      x^5 = x * x^4 := by ring
      _ = x * (48 * x - 28) := by rw [eq3]
      _ = 48 * x^2 - 28 * x := by nlinarith
      _ = 48 * (4 * x - 2) - 28 * x := by rw [eq1]
      _ = 164 * x - 96 := by nlinarith
  rw [show x^5 = 164 * x - 96 by linarith [eq4]]
  rw [show x^2 = 4 * x - 2 by linarith [eq1]]
  nlinarith