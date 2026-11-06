import Mathlib

theorem number_theory_227175 :
    IsLeast {n | ∃ k, n = ∑ i ∈ Finset.range 5, (2 * i + 2 * k) ∧ 7 ∣ n} 70 := by
  constructor
  · -- Show 70 is in the set.
    use 5
    native_decide
  · -- Show no smaller n is in the set.
    intro n hn
    rcases hn with ⟨k, hn_eq, hn_div⟩
    have h1 : n = 10 * k + 20 := by
      simp [Finset.sum_range_succ, Finset.sum_range_zero] at hn_eq
      omega
    rw [h1] at hn_div
    by_contra h
    push_neg at h
    have h2 : k < 5 := by
      omega
    have h3 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
      omega
    rcases h3 with (rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num at hn_div