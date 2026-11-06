import Mathlib

open Real

/- 286. Prove, without using logarithmic tables, that
a) $\frac{1}{\log _{2} \pi}+\frac{1}{\log _{5} \pi}>2$;
b) $\frac{1}{\log _{2} \pi}+\frac{1}{\log _{\pi} 2}>2$. -/
theorem inequalities_130342 :
    1 / logb 2 Real.pi + 1 / logb 5 Real.pi > 2 ∧
    1 / logb 2 Real.pi + 1 / logb Real.pi 2 > 2 := by
  constructor
  · -- Proof for part a) $\frac{1}{\log _{2} \pi}+\frac{1}{\log _{5} \pi}>2$
    -- Rewrite the sum of reciprocals as a single fraction
    have h1 : 1 / logb 2 Real.pi + 1 / logb 5 Real.pi = (log 2 + log 5) / log Real.pi := by
      -- Convert 1/logb 2 π to log 2 / log π
      have h1 : 1 / logb 2 Real.pi = log 2 / log Real.pi := by
        field_simp [logb]
      -- Convert 1/logb 5 π to log 5 / log π
      have h2 : 1 / logb 5 Real.pi = log 5 / log Real.pi := by
        field_simp [logb]
      rw [h1, h2]
      ring
    rw [h1]
    -- Use the logarithm property: log(a) + log(b) = log(a*b)
    have h2 : log 2 + log 5 = log (2 * 5) := by
      rw [log_mul (by norm_num) (by norm_num)]
    rw [h2]
    -- Simplify 2*5 to 10
    have h3 : log (2 * 5 : ℝ) = log 10 := by norm_num
    rw [h3]
    -- Prove that π² < 10
    have h4 : Real.pi ^ 2 < 10 := by
      have h4 : Real.pi < 3.15 := Real.pi_lt_d2
      norm_num at h4
      nlinarith [h4, Real.pi_gt_three]
    -- Prove that log π > 0
    have h5 : log Real.pi > 0 := by
      apply log_pos
      linarith [Real.pi_gt_three]
    -- Prove that log 10 > 2*log π
    have h6 : log (10 : ℝ) > 2 * log Real.pi := by
      -- First show log 10 > log(π²)
      have h7 : log (10 : ℝ) > log (Real.pi ^ 2) := by
        have h8 : log (Real.pi ^ 2) < log (10 : ℝ) := by
          apply Real.log_lt_log
          nlinarith [Real.pi_gt_three]
          all_goals linarith
        linarith
      -- Then use log(π²) = 2*log π
      have h8 : log (Real.pi ^ 2 : ℝ) = 2 * log Real.pi := by
        simp [log_pow]
      linarith [h7, h8]
    -- Apply division to both sides of the inequality
    have h7 : (log (10 : ℝ) : ℝ) / log Real.pi > (2 * log Real.pi) / log Real.pi := by
      apply (div_lt_div_right h5).mpr
      linarith
    -- Simplify (2*log π)/log π to 2
    have h8 : (2 * log Real.pi) / log Real.pi = 2 := by
      have h8 : log Real.pi ≠ 0 := by
        linarith
      field_simp [h8]
    linarith [h7, h8]
  · -- Proof for part b) $\frac{1}{\log _{2} \pi}+\frac{1}{\log _{\pi} 2}>2$
    -- Rewrite the sum using the definition of logb
    have h1 : 1 / logb 2 Real.pi + 1 / logb Real.pi 2 = (log 2 / log Real.pi) + (log Real.pi / log 2) := by
      -- Convert 1/logb 2 π to log 2 / log π
      have h1 : 1 / logb 2 Real.pi = log 2 / log Real.pi := by
        field_simp [logb]
      -- Convert 1/logb π 2 to log π / log 2
      have h2 : 1 / logb Real.pi 2 = log Real.pi / log 2 := by
        field_simp [logb]
      rw [h1, h2]
    rw [h1]
    -- Prove log 2 > 0
    have h2 : log 2 > 0 := by
      apply log_pos
      all_goals linarith
    -- Prove log π > 0
    have h3 : log Real.pi > 0 := by
      apply log_pos
      all_goals linarith [Real.pi_gt_three]
    -- Prove that (log 2/log π) + (log π/log 2) > 2
    have h4 : (log 2 / log Real.pi) + (log Real.pi / log 2) > 2 := by
      -- Use the AM-GM inequality: for positive a and b, (a+b)/2 ≥ √(a*b) with equality iff a=b
      -- Rewrite the expression as 2 plus a positive term
      have h4 : (log 2 / log Real.pi) + (log Real.pi / log 2) - 2 = (log 2 - log Real.pi) ^ 2 / (log 2 * log Real.pi) := by
        field_simp
        ring
      -- Prove (log 2 - log π)² > 0 by showing log 2 ≠ log π
      have h5 : (log 2 - log Real.pi) ^ 2 > 0 := by
        have h5 : log 2 ≠ log Real.pi := by
          by_contra h
          -- If log 2 = log π, then 2 = π (contradiction)
          have h1 : (2 : ℝ) = Real.pi := by
            have h2 : log 2 = log Real.pi := by assumption
            have h3 : (2 : ℝ) > 0 := by norm_num
            have h4 : Real.pi > 0 := Real.pi_pos
            have h5 : (2 : ℝ) = Real.pi := by
              exact log_injOn_pos (by simp [h3]) (by simp [h4]) h2
            exact h5
          linarith [Real.pi_gt_three, h1]
        exact pow_two_pos_of_ne_zero (sub_ne_zero_of_ne h5)
      -- Prove log 2 * log π > 0
      have h6 : log 2 * log Real.pi > 0 := mul_pos h2 h3
      -- Prove the fraction is positive
      have h7 : (log 2 - log Real.pi) ^ 2 / (log 2 * log Real.pi) > 0 := by
        apply div_pos
        all_goals linarith
      linarith [h4, h7]
    linarith [h4]
