import Mathlib

theorem algebra_171049 (x y : ℝ) (h1 : 4^x + y = 4030) (h2 : 17 * 2^x + 2 * y = 2019) :
    x = Real.logb 2 ((17 + Real.sqrt 48617) / 4) ∧ y = (7787 - 17 * Real.sqrt 48617) / 8 := by
  have eq1 : y = 4030 - (4^x) := by
    linarith
  have eq2 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x) := by
    calc
      (4 : ℝ) ^ x = (2 ^ (2 : ℝ) ) ^ x := by norm_num
      _ = 2 ^ (2 * x) := by rw [← Real.rpow_mul]; ring; all_goals linarith
  have eq3 : (4 : ℝ) ^ x = ((2 : ℝ) ^ x) ^ 2 := by
    rw [eq2]
    have h3 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by
      calc
        (2 : ℝ) ^ (2 * x) = (2 : ℝ) ^ (x + x) := by ring_nf
        _ = ((2 : ℝ) ^ x) * (2 : ℝ) ^ x := by rw [← Real.rpow_add]; ring; all_goals linarith
        _ = ((2 : ℝ) ^ x) ^ 2 := by ring
    rw [h3]
  rw [eq1] at h2
  have eq4 : 2 * ((2 : ℝ) ^ x) ^ 2 - 17 * (2 : ℝ) ^ x - 6041 = 0 := by
    have eq5 : (4 : ℝ) ^ x = ((2 : ℝ) ^ x) ^ 2 := eq3
    nlinarith [h2, eq5]
  have h3 : ((2 : ℝ) ^ x) = (17 + Real.sqrt 48617) / 4 := by
    have h4 : 2 * ((2 : ℝ) ^ x) ^ 2 - 17 * (2 : ℝ) ^ x - 6041 = 0 := eq4
    have h5 : ((2 : ℝ) ^ x) > 0 := by positivity
    have h6 : ((2 : ℝ) ^ x - (17 + Real.sqrt 48617) / 4 ) * ((2 : ℝ) ^ x - (17 - Real.sqrt 48617) / 4 ) = 0 := by
      nlinarith [h4, Real.sqrt_nonneg 48617, Real.sq_sqrt (show (0 : ℝ) ≤ 48617 by norm_num)]
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where $2^x = \frac{17 + \sqrt{48617}}{4}$
      linarith 
    · -- Case where $2^x = \frac{17 - \sqrt{48617}}{4}$ 
      have h8 : (17 - Real.sqrt 48617) < 0 := by
        nlinarith [Real.sqrt_nonneg 48617, Real.sq_sqrt (show (0 : ℝ) ≤ 48617 by norm_num)]
      have h9 : (2 : ℝ) ^ x > 0 := by positivity
      nlinarith [Real.sqrt_nonneg 48617, h8, h9]
  have hx1 : x = Real.logb 2 ((17 + Real.sqrt 48617) / 4) := by
    have h4 : (2 : ℝ) ^ x = (17 + Real.sqrt 48617) / 4 := h3
    have hx2 : x = Real.logb 2 ((2 : ℝ) ^ x) := by
      rw [Real.logb_rpow]
      all_goals linarith
    rw [hx2]
    rw [h4]
  have hy1 : y = (7787 - 17 * Real.sqrt 48617) / 8 := by
    have eq1 : y = 4030 - (4^x) := by
      linarith
    have eq8 : (4 : ℝ) ^ x = ((17 + Real.sqrt 48617) / 4) ^ 2 := by
      have h42 : (2 : ℝ) ^ x = (17 + Real.sqrt 48617) / 4 := h3
      have eq3 : (4 : ℝ) ^ x = ((2 : ℝ) ^ x) ^ 2 := by
        rw [eq2]
        have h3 : (2 : ℝ) ^ (2 * x) = ((2 : ℝ) ^ x) ^ 2 := by
          calc
            (2 : ℝ) ^ (2 * x) = (2 : ℝ) ^ (x + x) := by ring_nf
            _ = ((2 : ℝ) ^ x) * (2 : ℝ) ^ x := by rw [← Real.rpow_add]; ring; all_goals linarith
            _ = ((2 : ℝ) ^ x) ^ 2 := by ring
        rw [h3]
      rw [eq3, h42]
      all_goals nlinarith
    rw [eq1, eq8]
    nlinarith [Real.sqrt_nonneg 48617, Real.sq_sqrt (show (0 : ℝ) ≤ 48617 by norm_num)]
  exact ⟨hx1, hy1⟩