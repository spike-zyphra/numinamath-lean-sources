import Mathlib

theorem algebra_313657 {a b c : ℝ}
    (ha : a = Real.sqrt 2006 - Real.sqrt 2005)
    (hb : b = Real.sqrt 2007 - Real.sqrt 2006)
    (hc : c = Real.sqrt 2008 - Real.sqrt 2007) :
    a > b ∧ b > c := by
  have h1 : a > b := by
    rw [ha, hb]
    have h2 : Real.sqrt 2006 - Real.sqrt 2005 > Real.sqrt 2007 - Real.sqrt 2006 := by
      have h5 : (Real.sqrt 2006 - Real.sqrt 2005) - (Real.sqrt 2007 - Real.sqrt 2006) > 0 := by
        have h6 : (Real.sqrt 2006 - Real.sqrt 2005) - (Real.sqrt 2007 - Real.sqrt 2006) =
            2 * Real.sqrt 2006 - Real.sqrt 2005 - Real.sqrt 2007 := by ring
        rw [h6]
        have h7 : (2 * Real.sqrt 2006 : ℝ) ^ 2 > (Real.sqrt 2005 + Real.sqrt 2007) ^ 2 := by
          have h8 : (2 * Real.sqrt 2006 : ℝ) ^ 2 = 4 * (Real.sqrt 2006) ^ 2 := by ring
          have h9 : (Real.sqrt 2006 : ℝ) ^ 2 = (2006 : ℝ) := Real.sq_sqrt (by norm_num)
          have h10 : (Real.sqrt 2005 + Real.sqrt 2007) ^ 2 = (Real.sqrt 2005 : ℝ) ^ 2 + (Real.sqrt 2007 : ℝ) ^ 2 + 2 * (Real.sqrt 2005 * Real.sqrt 2007) := by ring
          have h11 : (Real.sqrt 2005 : ℝ) ^ 2 = (2005 : ℝ) := Real.sq_sqrt (by norm_num)
          have h12 : (Real.sqrt 2007 : ℝ) ^ 2 = (2007 : ℝ) := Real.sq_sqrt (by norm_num)
          rw [h8, h9, h10, h11, h12]
          nlinarith [sq_nonneg (Real.sqrt 2006 ^ 2 - (2006 : ℝ)), sq_nonneg ((Real.sqrt 2005) ^ 2 - (2005 : ℝ)), sq_nonneg ((Real.sqrt 2007) ^ 2 - (2007 : ℝ)), Real.sqrt_nonneg 2005, Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007, mul_nonneg (Real.sqrt_nonneg 2005) (Real.sqrt_nonneg 2006), mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2007), Real.sqrt_nonneg (2005 * 2007), Real.sqrt_nonneg (2006 ^ 2)]
        have h8 : (2 * Real.sqrt 2006 : ℝ) > (Real.sqrt 2005 + Real.sqrt 2007) := by
          nlinarith [h7, mul_nonneg (Real.sqrt_nonneg 2005) (Real.sqrt_nonneg 2007), Real.sqrt_nonneg 2005, Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007]
        nlinarith [Real.sqrt_nonneg 2005, Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007]
      linarith
    linarith
  have h2 : b > c := by
    rw [hb, hc]
    have h3 : Real.sqrt 2007 - Real.sqrt 2006 > Real.sqrt 2008 - Real.sqrt 2007 := by
      have h5 : (Real.sqrt 2007 - Real.sqrt 2006) - (Real.sqrt 2008 - Real.sqrt 2007) > 0 := by
        have h7 : (Real.sqrt 2007 - Real.sqrt 2006) - (Real.sqrt 2008 - Real.sqrt 2007) = 2 * Real.sqrt 2007 - Real.sqrt 2006 - Real.sqrt 2008 := by ring
        rw [h7]
        have h7 : (2 * Real.sqrt 2007 : ℝ) ^ 2 > (Real.sqrt 2006 + Real.sqrt 2008) ^ 2 := by
          have h8 : (2 * Real.sqrt 2007 : ℝ) ^ 2 = 4 * (Real.sqrt 2007) ^ 2 := by ring
          have h9 : (Real.sqrt 2007 : ℝ) ^ 2 = (2007 : ℝ) := Real.sq_sqrt (by norm_num)
          have h10 : (Real.sqrt 2006 + Real.sqrt 2008) ^ 2 = (Real.sqrt 2006 : ℝ) ^ 2 + (Real.sqrt 2008 : ℝ) ^ 2 + 2 * (Real.sqrt 2006 * Real.sqrt 2008) := by ring
          have h11 : (Real.sqrt 2006 : ℝ) ^ 2 = (2006 : ℝ) := Real.sq_sqrt (by norm_num)
          have h12 : (Real.sqrt 2008 : ℝ) ^ 2 = (2008 : ℝ) := Real.sq_sqrt (by norm_num)
          rw [h8, h9, h10, h11, h12]
          nlinarith [sq_nonneg (Real.sqrt 2007 ^ 2 - (2007 : ℝ)), sq_nonneg ((Real.sqrt 2006) ^ 2 - (2006 : ℝ)), sq_nonneg ((Real.sqrt 2008) ^ 2 - (2008 : ℝ)), Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007, Real.sqrt_nonneg 2008, mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2007), mul_nonneg (Real.sqrt_nonneg 2007) (Real.sqrt_nonneg 2008), Real.sqrt_nonneg (2006 * 2008), Real.sqrt_nonneg (2007 ^ 2)]
        have h8 : (2 * Real.sqrt 2007 : ℝ) > Real.sqrt 2006 + Real.sqrt 2008 := by
          nlinarith [h7, mul_nonneg (Real.sqrt_nonneg 2006) (Real.sqrt_nonneg 2008), Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007, Real.sqrt_nonneg 2008]
        nlinarith [Real.sqrt_nonneg 2006, Real.sqrt_nonneg 2007, Real.sqrt_nonneg 2008]
      linarith
    linarith
  constructor
  · linarith
  · linarith