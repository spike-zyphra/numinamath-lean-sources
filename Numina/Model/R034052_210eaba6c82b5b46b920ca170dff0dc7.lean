import Mathlib
theorem number_theory_48566 :
    IsLeast {n | ∃ k m r : ℕ, n = k + m + r ∧ k > m ∧ m > r ∧ m * 91 > r * 92 ∧ r * 92 > k * 90} 413 := by
  constructor 
  · -- Show 413 is in the set.
    use 139, 138, 136
    all_goals norm_num
  · -- Show that 413 is the least.
    intro n hn
    rcases hn with ⟨k, m, r, hn_eq, hk1, hk2, hk3, hk4⟩
    by_contra h
    push_neg at h
    have h1 : k + m + r < 413 := by
      omega
    have h2 : k ≤ 412 := by
      omega
    have h3 : m ≤ 412 := by
      omega
    have h4 : r ≤ 412 := by
      omega
    interval_cases k <;> omega