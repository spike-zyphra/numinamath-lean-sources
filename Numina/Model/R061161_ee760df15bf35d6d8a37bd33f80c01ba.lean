import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_323712 :
  IsGreatest {x | ∃ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 5 ∧ x = 2*a + 2*a*b + a*b*c} 18 := by
  constructor
  · -- We need to show that 18 is in the set.
    use 3, 2, 0
    norm_num
  · -- We need to show that any x in the set is ≤ 18
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hsum, hx⟩
    have h1 : c = 5 - a - b := by linarith
    rw [h1] at hx
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 2), sq_nonneg (a + 2 * b - 5), sq_nonneg (a - 3), sq_nonneg (b - 2), sq_nonneg (5 - a - b), sq_nonneg (a * b - 6), sq_nonneg (a - 3), sq_nonneg (b - 2), mul_nonneg ha hb, mul_nonneg hb (show (5 - a - b) ≥ 0 by nlinarith [h1, ha, hb, hc]), mul_nonneg ha (show (5 - a - b) ≥ 0 by nlinarith [h1, ha, hb, hc]) ]