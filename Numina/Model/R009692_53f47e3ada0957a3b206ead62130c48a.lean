import Mathlib

theorem number_theory_4073 :
    IsGreatest {n | 10 ≤ n ∧ n < 100 ∧ 6 ∣ n^3 - n^2 - 100 * n + 100 ∧ ¬4 ∣ n^3 - n^2 - 100 * n + 100 ∧ ¬9 ∣ n^3 - n^2 - 100 * n + 100 } 95 := by
  constructor
  · -- Show that 95 is in the set.
    refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that 95 is the greatest such integer.
    intro n hn
    rcases hn with ⟨h1, h2, h3, h4, h5⟩
    by_contra h
    push_neg at h
    interval_cases n <;> try { norm_num at * } <;> omega