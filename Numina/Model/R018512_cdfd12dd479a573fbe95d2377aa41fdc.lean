import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_321028 (f : ℝ → ℝ) (hf : f = λ x => 2*x^2 - 4*x*sin x + 1) :
    {x | f x ≤ cos (2*x)} = {0} := by 
  ext x 
  simp [hf]
  constructor
  · -- Assume $f(x) \leq \cos(2x)$, prove $x = 0$.
    intro h 
    have h1 : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by 
      have hcos : cos (2 * x) = 1 - 2 * (sin x) ^ 2 := by 
        rw [cos_two_mul, sin_sq]
        <;> ring
      exact hcos 
    rw [h1] at h 
    have h2 : 2 * x^2 + 2 * (sin x) ^ 2 - 4 * x * (sin x) ≤ 0 := by
      nlinarith 
    have h3 : 2 * (x - sin x) ^ 2 ≤ 0 := by
      nlinarith
    have h4 : (x - sin x) ^ 2 ≤ 0 := by 
      nlinarith 
    have h5 : (x - sin x) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x - sin x), Real.sin_sq_add_cos_sq x]
    have h6 : x - sin x = 0 := by
      exact pow_eq_zero h5 
    have h7 : x = sin x := by
      linarith
    have h8 : x = 0 := by 
      by_cases h9 : x > 0 
      · -- Assume x > 0 
        have h10 : sin x < x := by 
          apply sin_lt
          all_goals 
            linarith 
        nlinarith
      by_cases h11 : x < 0 
      · -- Assume x < 0 
        have h12 : sin x > x := by 
          have h13 : sin (-x) < -x := by 
            apply sin_lt
            all_goals 
              have h14 : -x > 0 := by linarith 
              all_goals 
                linarith 
          have h14 : -x > 0 := by linarith 
          have h15 : sin x > x := by
            have h16 : sin (-x) = -sin x := by 
              rw [show sin (-x) = -sin x by simp [sin_neg]]
            linarith [h13, h16]
          linarith 
        nlinarith
      linarith [Real.sin_le_one x, Real.sin_le_one x]
    exact h8 
  · -- Assume x = 0 
    intro h 
    rw [h] 
    norm_num [Real.sin_zero, Real.cos_zero]