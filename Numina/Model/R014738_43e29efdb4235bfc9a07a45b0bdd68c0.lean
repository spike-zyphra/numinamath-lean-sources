import Mathlib

theorem number_theory_228962 (n : ℕ) (h : n = 3000003) :
    ∃ d e, d < 10 ∧ e < 10 ∧ 13 ∣ n + d * 100 + e * 10000 := by
  subst h
  use 8, 0
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num