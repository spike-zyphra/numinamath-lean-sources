import Mathlib

theorem number_theory_609168 (h : 62 ^ 2 + 122 ^ 2 = 18728) : (30, 92) ∈ {(n, m) : ℕ × ℕ | n > 0 ∧ m > 0 ∧ n ^ 2 + m ^ 2 = 9364} := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num