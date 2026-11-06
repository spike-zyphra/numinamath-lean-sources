import Mathlib

theorem number_theory_95583 :
IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 18, (k + i) ∧ ∃ m, m^2 = n} 225 := by
  constructor
  · -- Show 225 is in this set
    use 4
    constructor
    · -- Show that 225 equals the sum
      norm_num [Finset.sum_range_succ]
    · -- Show that there exists m such that m^2 = 225
      use 15
      all_goals norm_num
  · -- Show 225 is the smallest such sum
    intro n hn
    rcases hn with ⟨k, h1, ⟨m, h2⟩⟩
    have h3 : n = ∑ i ∈ Finset.range 18, (k + i) := by linarith [h1]
    have h4 : n = 18 * k + 153 := by
      rw [h3]
      norm_num [Finset.sum_range_succ]
      <;> ring
    have h5 : m ^ 2 = 18 * k + 153 := by
      linarith [h2, h4]
    by_contra h
    push_neg at h
    have h6 : n < 225 := by linarith
    have h7 : k < 4 := by
      omega
    have h8 : m ^ 2 < 225 := by
      nlinarith [h6, h4]
    have h9 : m ≤ 14 := by
      nlinarith
    interval_cases m <;> omega