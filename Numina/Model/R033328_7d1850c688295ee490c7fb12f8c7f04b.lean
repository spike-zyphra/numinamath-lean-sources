import Mathlib

open Real

/- If $\sqrt{12}+\sqrt{75}>n$, where $n$ is an integer, find the maximum value of $n$.

 -/
theorem inequalities_3120 : IsGreatest {n : ℤ | n < √12 + √75} 12 := by
  constructor
  · -- Show that 12 is in the set, i.e., 12 < √12 + √75
    have h1 : √12 + √75 > (12 : ℝ) := by
      have h2 : √12 + √75 > 0 := by
        have h12 : √12 > 0 := by
          apply Real.sqrt_pos.mpr
          all_goals norm_num
        have h75 : √75 > 0 := by
          apply Real.sqrt_pos.mpr
          all_goals norm_num
        linarith
      have h3 : (√12 + √75) ^ 2 > (12 : ℝ) ^ 2 := by
        have h4 : (√12 + √75) ^ 2 = (√12) ^ 2 + (√75) ^ 2 + 2 * (√12 * √75) := by ring
        rw [h4]
        have h5 : (√12) ^ 2 = (12 : ℝ) := Real.sq_sqrt (by norm_num)
        have h6 : (√75) ^ 2 = (75 : ℝ) := Real.sq_sqrt (by norm_num)
        have h7 : √12 * √75 = (30 : ℝ) := by
          calc
            √12 * √75 = √(12 * 75 : ℝ) := by
              rw [Real.sqrt_mul (by norm_num)]
            _ = √(900 : ℝ) := by
              norm_num
            _ = (30 : ℝ) := by
              rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h5, h6, h7]
        norm_num
      have h4' : (√12 + √75) > 0 := by
        positivity
      have h5 : (12 : ℝ) > 0 := by
        norm_num
      nlinarith [h4']
    have h2 : (12 : ℤ) < √12 + √75 := by
      exact_mod_cast h1
    simpa using h2
  · -- Show that 12 is greatest
    intro n hn
    have h3 : (n : ℝ) < √12 + √75 := by
      simpa using hn
    by_contra h
    push_neg at h
    have h4 : n ≥ 13 := by
      omega
    have h5 : (n : ℝ) ≥ (13 : ℝ) := by
      exact_mod_cast h4
    have h6 : √12 + √75 < (13 : ℝ) := by
      nlinarith [Real.sqrt_nonneg 12, Real.sqrt_nonneg 75, 
                  Real.sq_sqrt (show (0 : ℝ) ≤ 12 by norm_num), 
                  Real.sq_sqrt (show (0 : ℝ) ≤ 75 by norm_num), 
                  mul_nonneg (Real.sqrt_nonneg 12) (Real.sqrt_nonneg 75), 
                  sq_nonneg (√12 + √75 - 13)
                ]
    nlinarith