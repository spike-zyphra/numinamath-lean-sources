import Mathlib

open Real Set
open scoped BigOperators

/- 3. Solve the inequality:

$$
x^{2}+4 x \sqrt{x+6} \leqslant 5(x+6)
$$ -/
theorem inequalities_107004 (x : ℝ) (hx : x ≥ -6) :
    x^2 + 4 * x * sqrt (x + 6) ≤ 5 * (x + 6) ↔ x ∈ Icc (-5) 3 := by
  constructor
  · -- Assume x^2 + 4 * x * sqrt (x + 6) ≤ 5 * (x + 6)
    intro h
    -- First we prove that x ≥ -5
    have h1 : -5 ≤ x := by
      by_contra h2
      push_neg at h2
      -- If x < -5, then sqrt(x+6) < 1
      have h3 : sqrt (x + 6) < 1 := by
        have h5 : sqrt (x + 6) < sqrt 1 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
        rw [show sqrt 1 = (1 : ℝ) by rw [Real.sqrt_one]] at h5
        linarith
      -- This leads to a contradiction with the original inequality
      nlinarith [Real.sq_sqrt (show 0 ≤ x + 6 from by linarith), sq_nonneg (x + 6), sq_nonneg (sqrt (x + 6)), h]
    -- Next we prove that x ≤ 3
    have h2 : x ≤ 3 := by
      by_contra h3
      push_neg at h3
      -- If x > 3, then sqrt(x+6) > 3
      have h4 : sqrt (x + 6) > 3 := by
        have h6 : sqrt (x + 6) > sqrt 9 := Real.sqrt_lt_sqrt (by linarith) (by linarith)
        have h7 : sqrt 9 = 3 := Real.sqrt_eq_cases.mpr (by norm_num)
        linarith
      -- This leads to a contradiction with the original inequality
      nlinarith [Real.sq_sqrt (show 0 ≤ x + 6 from by linarith), sq_nonneg (x + 6), sq_nonneg (sqrt (x + 6)), h]
    -- Combine the bounds to show x ∈ [-5, 3]
    constructor
    · linarith [h1]
    · linarith [h2]
  · -- Now we prove the reverse direction: if x ∈ [-5, 3], then x^2 + 4 * x * sqrt (x + 6) ≤ 5 * (x + 6)
    rintro ⟨h1, h2⟩
    -- If x ∈ [-5, 3], then 1 ≤ sqrt(x+6)
    have h3 : 1 ≤ sqrt (x + 6) := by
      have h5 : sqrt (x + 6) ≥ sqrt 1 := Real.sqrt_le_sqrt (by linarith)
      have h6 : sqrt 1 = 1 := Real.sqrt_one
      linarith
    -- If x ∈ [-5, 3], then sqrt(x+6) ≤ 3
    have h4 : sqrt (x + 6) ≤ 3 := by
      have h6 : sqrt (x + 6) ≤ sqrt 9 := Real.sqrt_le_sqrt (by linarith)
      have h7 : sqrt 9 = 3 := Real.sqrt_eq_cases.mpr (by norm_num)
      linarith
    -- Use these bounds to prove the original inequality
    nlinarith [Real.sq_sqrt (show 0 ≤ x + 6 from by linarith), sq_nonneg (x + 6), sq_nonneg (sqrt (x + 6)), h3, h4]
