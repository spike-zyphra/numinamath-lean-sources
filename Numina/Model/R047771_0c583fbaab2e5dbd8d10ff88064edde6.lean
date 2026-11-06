import Mathlib

theorem algebra_177676 (a : ℝ) (x : ℝ) (hx : x ≥ 0) :
    x = a + Real.sqrt (a + Real.sqrt x) ↔ x = a + Real.sqrt x := by 
  constructor
  · -- Assume x = a + Real.sqrt (a + Real.sqrt x) holds, prove x = a + Real.sqrt x.
    intro h_eq
    have h2 : x ≥ a := by
      have h3 : Real.sqrt (a + Real.sqrt x) ≥ 0 := Real.sqrt_nonneg (a + Real.sqrt x)
      linarith [h_eq, h3]
    have h3 : Real.sqrt (a + Real.sqrt x) = x - a := by
      nlinarith [h_eq, Real.sqrt_nonneg (a + Real.sqrt x)]
    have h4 : a + Real.sqrt x ≥ 0 := by
      by_contra h
      push_neg at h
      have h5 : Real.sqrt (a + Real.sqrt x) = 0 := by
        have h6 : a + Real.sqrt x < (0 : ℝ) := by linarith
        have h7 : Real.sqrt (a + Real.sqrt x) = 0 := by
          rw [Real.sqrt_eq_zero']
          nlinarith
        linarith
      have h8 : x = a := by
        nlinarith [h5, h_eq]
      have h9 : Real.sqrt x = Real.sqrt a := by
        rw [h8]
      have h10 : a ≥ 0 := by
        by_contra h
        push_neg at h
        have h11 : Real.sqrt a = (0 : ℝ) := by
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith
        have h12 : Real.sqrt x = 0 := by
          nlinarith [h9, h11]
        have h13 : x = (0 : ℝ) := by
          calc
            x = (Real.sqrt x) ^ 2 := by rw [Real.sq_sqrt hx]
            _ = (0 : ℝ) ^ 2 := by rw [h12]
            _ = (0 : ℝ) := by norm_num
        have h14 : a = (0 : ℝ) := by
          nlinarith [h13, h8]
        nlinarith [h14, show (0 : ℝ) < (0 + 1 : ℝ) by norm_num, h]
      nlinarith [Real.sqrt_nonneg x, h9, Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sqrt_nonneg a]
    have h5 : (Real.sqrt (a + Real.sqrt x)) ^ 2 = (x - a) ^ 2 := by
      rw [h3]
    have h6 : (Real.sqrt (a + Real.sqrt x)) ^ 2 = (a + Real.sqrt x) := by
      have h4' : a + Real.sqrt x ≥ 0 := h4
      rw [Real.sq_sqrt h4']
    nlinarith [h6, h5, Real.sqrt_nonneg (a + Real.sqrt x), Real.sqrt_nonneg x, Real.sq_sqrt hx]
  · -- Assume x = a + Real.sqrt x.
    intro h_eq
    have h1 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
    have h2 : a + Real.sqrt x ≥ 0 := by
      nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt hx, h_eq]
    have h3 : a + Real.sqrt x = x := by
      nlinarith [h_eq, Real.sqrt_nonneg x, Real.sq_sqrt hx]
    have h4 : Real.sqrt (a + Real.sqrt x) = Real.sqrt x := by
      rw [h3]
    nlinarith [h_eq, h4, Real.sqrt_nonneg x, Real.sq_sqrt hx]