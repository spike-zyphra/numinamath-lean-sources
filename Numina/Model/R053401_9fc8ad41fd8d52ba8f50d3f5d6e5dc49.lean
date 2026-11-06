import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_227235 :
  IsGreatest {z | ∃ x y : ℝ, z = x * y ∧ sqrt (x + y - 1) + x^4 + y^4 - 1 / 8 ≤ 0} 0.25 := by
  constructor
  · -- First we verify that 0.25 is achievable by showing that x = y = 0.5 satisfies the inequality
    use 0.5, 0.5
    norm_num [sqrt_eq_zero']
    all_goals norm_num
  · -- Now we prove that 0.25 is indeed the greatest such value
    intro z h
    rcases h with ⟨x, y, hz, hineq⟩
    have h1 : sqrt (x + y - 1) ≥ 0 := Real.sqrt_nonneg (x + y - 1)
    have h3 : x^4 + y^4 ≥ 2 * (x * y)^2 := by
      nlinarith [sq_nonneg (x^2 - y^2)]
    have h4 : x^4 + y^4 ≤ 1 / 8 := by 
      nlinarith [h1, h3, hineq]
    have h5 : (x * y) ^ 2 ≤ (1 / 16 : ℝ) := by 
      nlinarith [h3, h4]
    have h6 : x * y ≤ (1 / 4 : ℝ) := by
      nlinarith [sq_nonneg (x * y - 1 / 4), h5]
    rw [hz]
    norm_num at h6 ⊢
    linarith