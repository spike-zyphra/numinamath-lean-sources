import Mathlib

theorem number_theory_199194 :
    IsLeast {k | ∃ m n, m > 0 ∧ n > 0 ∧ 3 * n^3 = 5 * m^2 ∧ k = m + n} 60 := by
  constructor
  · -- Show that 60 is in the set
    use 45, 15
    all_goals norm_num
  · -- Show that for all elements k in the set, k >= 60
    intro k hk
    rcases hk with ⟨m, n, hm_pos, hn_pos, h_eq, hk_eq⟩
    by_contra h
    push_neg at h
    have h1 : m + n < 60 := by linarith
    have h2 : m ≤ 59 := by omega
    have h3 : n ≤ 59 := by omega
    interval_cases m <;> interval_cases n
    <;> omega