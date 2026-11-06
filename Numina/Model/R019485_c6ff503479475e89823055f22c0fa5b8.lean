import Mathlib

theorem algebra_298043 (a b c : ℝ × ℝ)
    (ha : √(a.1^2 + a.2^2) = 1) (hb : √(b.1^2 + b.2^2) = 1)
    (hc : √(c.1^2 + c.2^2) = 1) (hperp : a.1 * b.1 + a.2 * b.2 = 0) :
    (c.1 - a.1) * (c.1 - b.1) + (c.2 - a.2) * (c.2 - b.2) ≤ 1 + Real.sqrt 2 := by
  have ha1 : a.1^2 + a.2^2 = 1 := by
    calc
      a.1^2 + a.2^2 = (√(a.1^2 + a.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1^2 := by rw [ha]
      _ = 1 := by norm_num
  have hb1 : b.1^2 + b.2^2 = 1 := by
    calc
      b.1^2 + b.2^2 = (√(b.1^2 + b.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1^2 := by rw [hb]
      _ = 1 := by norm_num
  have hc1 : c.1^2 + c.2^2 = 1 := by
    calc
      c.1^2 + c.2^2 = (√(c.1^2 + c.2^2)) ^ 2 := by rw [Real.sq_sqrt]; positivity
      _ = 1^2 := by rw [hc]
      _ = 1 := by norm_num
  have eq1 : (c.1 - a.1) * (c.1 - b.1) + (c.2 - a.2) * (c.2 - b.2) = 
      1 - ( (c.1 * b.1 + c.2 * b.2) + (a.1 * c.1 + a.2 * c.2) ) := by
    nlinarith 
  have eq2 : (c.1 * b.1 + c.2 * b.2) + (a.1 * c.1 + a.2 * c.2) = 
      c.1 * (a.1 + b.1) + c.2 * (a.2 + b.2) := by
    ring 
  have eq4 : (c.1 * (a.1 + b.1) + c.2 * (a.2 + b.2)) ^ 2 ≤ 2 := by
    have h2 : (a.1 + b.1)^2 + (a.2 + b.2)^2 = 2 := by
      have h2 : a.1 ^2 + a.2 ^2 = 1 := ha1
      have h3 : b.1 ^2 + b.2 ^2 = 1 := hb1
      have h4 : a.1 * b.1 + a.2 * b.2 = 0 := hperp
      nlinarith 
    nlinarith [sq_nonneg (c.1 * (a.2 + b.2) - c.2 * (a.1 + b.1)), sq_nonneg (c.1 ^2 + c.2 ^2 - 1), sq_nonneg ((a.1 + b.1) ^2 + (a.2 + b.2) ^2 - 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have eq5 : c.1 * (a.1 + b.1) + c.2 * (a.2 + b.2) ≥ -Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (c.1 * (a.1 + b.1) + c.2 * (a.2 + b.2) + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  rw [eq1, eq2]
  nlinarith [eq5]