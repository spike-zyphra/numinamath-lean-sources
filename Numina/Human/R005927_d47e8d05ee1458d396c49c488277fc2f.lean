import Mathlib

/-Given that the 32-digit integer
$ 64312311692944269609355712372657 $
is the product of 6 consecutive primes, compute the sum of these 6 primes.-/
theorem number_theory_610749 : 64312311692944269609355712372657 = 200131 * 200153 * 200159 * 200171 * 200177 * 200183
  ∧ Nat.Prime 200131 ∧ Nat.Prime 200153 ∧ Nat.Prime 200159 ∧ Nat.Prime 200171 ∧ Nat.Prime 200177 ∧ Nat.Prime 200183
  ∧ 200131 + 200153 + 200159 + 200171 + 200177 + 200183 = 1200974 := by
  -- Answer: 1200974
  norm_num