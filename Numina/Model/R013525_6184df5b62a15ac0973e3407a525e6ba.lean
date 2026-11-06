import Mathlib

theorem algebra_305080 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (1 - Real.sqrt (1 + x)) = x ↔ x = 0 := by
  constructor
  · -- Assume $\sqrt{1-\sqrt{1+x}}=x$, prove $x=0$
    intro h
    by_cases h1 : 1 - Real.sqrt (1 + x) ≥ 0
    · -- Case where $1 - Real.sqrt (1 + x) \geq 0$
      have h2 : Real.sqrt (1 - Real.sqrt (1 + x)) = x := h
      have h3 : 1 - Real.sqrt (1 + x) = x ^ 2 := by
        calc
          1 - Real.sqrt (1 + x) = (Real.sqrt (1 - Real.sqrt (1 + x))) ^ 2 := by
            rw [Real.sq_sqrt]
            linarith [h1]
          _ = (x) ^ 2 := by
            rw [h2]
          _ = x ^ 2 := by ring
      have h4 : Real.sqrt (1 + x) = 1 - x^2 := by 
        nlinarith 
      have h6 : (Real.sqrt (1 + x)) ^ 2 = 1 + x := by
        rw [Real.sq_sqrt]
        nlinarith 
      have h7 : (1 - x^2) ^ 2 = 1 + x := by
        rw [show Real.sqrt (1 + x) = 1 - x^2 by linarith [h4]] at h6 
        linarith
      have h8 : x * (x ^ 3 - 2 * x - 1) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h8) with h9 h10
      · -- Case where $x = 0$
        linarith
      · -- Case where $x^3 - 2 x - 1 = 0$
        have h8_eq : x ≤ 0 := by
          have h11 : Real.sqrt (1 + x) ≤ 1 := by
            nlinarith [Real.sqrt_nonneg (1 + x), h1]
          have h12 : (Real.sqrt (1 + x)) ^ 2 ≤ (1 : ℝ) := by
            nlinarith [h11, Real.sqrt_nonneg (1 + x)]
          have h13 : (Real.sqrt (1 + x)) ^ 2 = 1 + x := by
            rw [Real.sq_sqrt]
            nlinarith
          nlinarith [h13, h12]
        have h8_eq2 : x = 0 := by linarith [hx, h8_eq]
        rw [h8_eq2] at h10
        nlinarith
    · -- Case where $1 - Real.sqrt (1 + x) < 0$
      have h2 : Real.sqrt (1 - Real.sqrt (1 + x)) = 0 := by
        rw [Real.sqrt_eq_zero']
        nlinarith
        all_goals nlinarith
      have h3 : x = 0 := by
        nlinarith [h, h2]
      have h4 : Real.sqrt (1 + x) = 1 := by
        rw [h3]
        norm_num
      have h6 : (1 - Real.sqrt (1 + x) < (0 : ℝ)) := by 
        nlinarith 
      rw [h4] at h6
      nlinarith
  · -- Assume x = 0, prove sqrt (1 - sqrt (1 + x)) = x
    intro h
    rw [h]
    norm_num