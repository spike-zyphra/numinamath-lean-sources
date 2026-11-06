import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_150327 :
  IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 5 ∧ x = 2*a + 2*a*b + a*b*c} 18 := by
  constructor
  · -- Let's prove 18 belongs to the set.
    use 3, 2, 0
    norm_num
  · -- Now, we need to show that 18 is the maximum possible value of $S$.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : c = 5 - a - b := by linarith
    rw [h2] at hx
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 2), sq_nonneg ((5 - a - b) : ℝ), 
      mul_nonneg ha hb, mul_nonneg hb (show (0 : ℝ) ≤ 5 - a - b by linarith), 
      mul_nonneg ha (show (0 : ℝ) ≤ 5 - a - b by linarith)]