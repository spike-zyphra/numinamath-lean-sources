import Mathlib

theorem inequalities_598940 (a b c : ℝ) (h : a + b + c = 0) :
    a^2 * b^2 + b^2 * c^2 + c^2 * a^2 + 3 ≥ 6 * a * b * c := by 
  have h1 : c = -a - b := by linarith
  have h2 : a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a ^ 2 + b ^ 2 + a * b) := by
    rw [show c = -a - b by linarith]
    nlinarith
  by_cases h3 : a ^ 2 + b ^ 2 + c ^ 2 ≤ 2
  · -- case 1: if $a^2 + b^2 + c^2 \leq 2$, prove the original inequality
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), 
          sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1), 
          h2, h3, sq_nonneg (a * b + b * c + c * a)]
  · -- case 2: if $a^2 + b^2 + c^2 > 2$, prove the original inequality
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a - c), sq_nonneg (b - c), 
          sq_nonneg (a * b), sq_nonneg (a * c), sq_nonneg (b * c), 
          sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c + 1), 
          h2, sq_nonneg (a * b + b * c + c * a)]