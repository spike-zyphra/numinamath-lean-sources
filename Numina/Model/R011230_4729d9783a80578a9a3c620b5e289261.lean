import Mathlib
open Polynomial

theorem algebra_7075 (p : Polynomial ℝ) (hp : p = 6 * X^6 - 5 * X^5 + 4 * X^4 - 10 * X^3 + 4 * X^2 - 5 * X + 6) : ∑ᶠ (x : ℝ) (_ : p.eval x = 0), x = 1 := by

  have h1 : ∀ x : ℝ, p.eval x = 6 * x^6 - 5 * x^5 + 4 * x^4 - 10 * x^3 + 4 * x^2 - 5 * x + 6 := by
    intro x 
    rw [hp]
    simp

  have h2 : p.eval 1 = 0 := by
    rw [h1 1]
    norm_num
  
  have h3 : ∀ x : ℝ, p.eval x = 0 → x = 1 := by
    intro x hx 
    rw [h1 x] at hx 
    have h_eq : 6 * x^6 - 5 * x^5 + 4 * x^4 - 10 * x^3 + 4 * x^2 - 5 * x + 6 = 0 := hx 
    have h_eq2 : (x - 1) ^ 2 * (6 * x^4 + 7 * x^3 + 12 * x^2 + 7 * x + 6) = 0 := by 
      nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (x^2 - x), sq_nonneg (x^2 + x), sq_nonneg (x^3 - x^2), sq_nonneg (x^3 + x^2)]

    cases' (mul_eq_zero.mp h_eq2) with h4 h5 
    · -- Case (x - 1) ^ 2 = 0 
      have : x - 1 = 0 := by 
        apply pow_eq_zero 
        exact h4 
      linarith 
    · -- Case 6 * x^4 + 7 * x^3 + 12 * x^2 + 7 * x + 6 = 0 
      nlinarith [sq_nonneg (x^2), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2 + 1), sq_nonneg (x^2 - x), sq_nonneg (x^2 + x), sq_nonneg (x^3 - x^2), sq_nonneg (x^3 + x^2), sq_nonneg (x^2 * (x + 1)), sq_nonneg (x * (x + 1))]
  
  have h4 : {x : ℝ | p.eval x = 0} = {1} := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] 
    constructor 
    · -- Assume p.eval x = 0, prove x = 1 
      intro h 
      apply h3 x h 
    · -- Assume x = 1, prove p.eval x = 0 
      intro h 
      rw [h] 
      exact h2
  
  rw [show ∑ᶠ (x : ℝ) (_ : p.eval x = 0), x = ∑ᶠ (x ∈ {x : ℝ | p.eval x = 0}), x by simp]
  rw [h4] 
  simp