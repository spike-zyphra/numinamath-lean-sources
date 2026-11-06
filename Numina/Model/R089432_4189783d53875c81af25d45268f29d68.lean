import Mathlib

theorem number_theory_163044 : ∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ p < q ∧ q < r ∧ p * q * r = 989 * 1001 * 1007 + 320 := by
  use 991, 997, 1009
  all_goals norm_num