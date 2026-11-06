import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_45589 :
  IsGreatest {x | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a ≤ 1 ∧ b ≤ 1 ∧ x = (a - b^2)*(b - a^2)} (1/16) := by 
  constructor
  · -- Show that 1/16 is in the set 
    use 1/2, 1/2 
    norm_num
  · -- Show that 1/16 is an upper bound
    intro x hx
    rcases hx with ⟨a, b, ha1, hb1, ha4, hb4, hx_eq⟩
    have h1 : (a - b^2) * (b - a^2) ≤ 1/16 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a - 1/2), sq_nonneg (b - 1/2), mul_nonneg (show (0 : ℝ) ≤ a by linarith) (show (0 : ℝ) ≤ 1 - a by linarith), mul_nonneg (show (0 : ℝ) ≤ b by linarith) (show (0 : ℝ) ≤ 1 - b by linarith)]
    linarith