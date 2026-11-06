import Mathlib
/- Find the smallest positive integer $n$ such that $\frac{5^{n+1}+2^{n+1}}{5^{n}+2^{n}}>4.99$. -/
theorem algebra_609110 : IsLeast {n : ℕ | ((5 : ℝ) ^ (n + 1) + 2 ^ (n + 1)) / (5 ^ n + 2 ^ n) > 4.99} 7:= by
  constructor
  -- First part: prove that 7 satisfies the inequality
  .
    simp
    norm_num
  -- Second part: prove that no number less than 7 satisfies the inequality
  .
    simp [lowerBounds]
    intro n hn
    -- Rewrite the numerator using distributive property
    rw [show (5 : ℝ) ^ (n + 1) + 2 ^ (n + 1) = 5 ^ n * 5 + 2 ^ n * 2 by ring] at hn
    by_contra H
    simp at H
    -- If n satisfies the inequality, it must be ≤ 6
    replace H : n ≤ 6:= by linarith
    -- Key inequality: 0.01 * 5^n ≤ 2.99 * 2^n
    have h1 : 0.01 * (5 : ℝ) ^ n ≤ 2.99 * 2 ^ n:= by
      norm_num
      -- Prove 2^n is positive
      have g1 : (2 : ℝ) ^ n > 0:= by positivity
      -- Transform the inequality using multiplication and division
      suffices 1 / 100 * (5 : ℝ) ^ n  / 2 ^ n ≤ 299 / 100 by exact (mul_inv_le_iff₀ g1).mp this
      rw [show 1 / 100 * (5 : ℝ) ^ n  / 2 ^ n = 1 / 100 * ((5 : ℝ) ^ n  / 2 ^ n) by ring]
      suffices (5 : ℝ) ^ n / 2 ^ n ≤ 299 by linarith
      -- Simplify the fraction of powers
      rw [show (5 : ℝ) ^ n / 2 ^ n = (5 / 2) ^ n by field_simp]
      -- Use the fact that n ≤ 6 and (5/2)^n is increasing
      suffices ((5 : ℝ) / 2) ^ n ≤ (5 / 2) ^ 6 by linarith
      refine pow_le_pow_right₀ (by linarith) H
    -- Show that the original fraction is ≤ 4.99
    replace h1 : (5 : ℝ) ^ n * 5 + 2 ^ n * 2 ≤ 4.99 * (5 ^ n + 2 ^ n):= by
      norm_num
      norm_num at h1
      linarith
    -- Prove denominator is positive
    have h2 : (5 : ℝ) ^ n + 2 ^ n > 0:= by positivity
    -- Final step: show contradiction with the assumption
    replace h1 : ((5 : ℝ) ^ n * 5 + 2 ^ n * 2) / ((5 : ℝ) ^ n + 2 ^ n) ≤ 4.99:= by exact (div_le_iff₀ h2).mpr h1
    linarith
