import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_173063 (f : ℝ → ℝ) (hf : f = λ x => (1 - x + sqrt (2 * x ^ 2 - 2 * x + 1)) / (2 * x)) :
    IsGreatest {y | ∃ x, 2 ≤ x ∧ x ≤ 3 ∧ f x = y} ((Real.sqrt 5 - 1) / 4) := by
  constructor
  · -- Show that (sqrt(5) - 1) / 4 is in the set
    use 2
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show that f 2 = (Real.sqrt 5 - 1) / 4
      rw [hf]
      have h1 : Real.sqrt (2 * (2:ℝ) ^ 2 - 2 * (2:ℝ) + 1) = Real.sqrt 5 := by norm_num
      simp [h1]
      all_goals ring
  · -- Show that (sqrt(5) - 1) / 4 is greatest
    intro y hy
    rcases hy with ⟨x, hx1, hx2, h_eq⟩
    rw [hf] at h_eq
    have h1 : (1 - x + Real.sqrt (2 * x ^ 2 - 2 * x + 1)) / (2 * x) = y := by
      simpa using h_eq
    -- Now we have $y = \frac{1 - x + \sqrt{2 x^2 - 2 x + 1}}{2 x}$ with $2 \leq x \leq 3$, need to show $y \leq \frac{\sqrt 5 - 1}{4}$.
    have h2 : 0 < x := by nlinarith
    have h3 : x ≥ (2:ℝ) := by linarith
    -- Show that f(x) ≤ (sqrt 5 - 1) / 4
    have h4 : (1 - x + Real.sqrt (2 * x ^ 2 - 2 * x + 1)) / (2 * x) ≤ (Real.sqrt 5 - 1) / 4 := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg (2 * x ^ 2 - 2 * x + 1), Real.sqrt_nonneg 5, 
          sq_nonneg (x - 2), sq_nonneg (Real.sqrt (2 * x ^ 2 - 2 * x + 1) - Real.sqrt 5), 
          Real.sqrt_nonneg (2 * x ^ 2 - 2 * x + 1), Real.sqrt_nonneg 5, 
          sq_nonneg (x - (2:ℝ)), 
          mul_nonneg (show (0 : ℝ) ≤ x - 2 by nlinarith) (show (0 : ℝ) ≤ (3 - x: ℝ) by nlinarith), 
          Real.sq_sqrt (show 0 ≤ (2 * x ^ 2 - 2 * x + 1 : ℝ) by nlinarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (5: ℝ) by norm_num), 
          Real.sqrt_nonneg (2 * x ^ 2 - 2 * x + 1), Real.sqrt_nonneg 5, 
          sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (Real.sqrt (2 * x ^ 2 - 2 * x + 1) - Real.sqrt 5)]
    linarith [h1, h4]