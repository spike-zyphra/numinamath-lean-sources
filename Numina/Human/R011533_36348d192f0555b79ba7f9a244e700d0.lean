import Mathlib

/-The sum of seven different natural numbers is 2n.
Is it true that there will definitely be three numbers among these seven numbers whose sum is greater than n?-/

theorem number_theory_138433: ∃ n a b c d e f g: ℕ, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ f < g ∧
  a + b + c + d + e + f + g = 2 * n ∧ e + f + g ≤ n := by

  -- we directly construct a counterexample
  use 50
  use 11
  use 12
  use 13
  use 14
  use 15
  use 16
  use 19
  norm_num