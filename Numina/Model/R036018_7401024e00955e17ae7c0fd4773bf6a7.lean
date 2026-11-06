import Mathlib

theorem number_theory_129948 {n : ℕ} (hn : n > 2000 ∧ n < 2500)
    (h : ∀ k ∈ Finset.Icc 2 7, n % k = 1) :
    IsLeast {x | ∃ m, x > 1 ∧ n % x = 0 ∧ m > 0 ∧ n = m * x} 11 := by
  rcases hn with ⟨h1, h2⟩
  have h2101 : n = 2101 := by
    have h2 := h 2 (by norm_num)
    have h3 := h 3 (by norm_num)
    have h4 := h 4 (by norm_num)
    have h5 := h 5 (by norm_num)
    have h6 := h 6 (by norm_num)
    have h7 := h 7 (by norm_num)
    interval_cases n <;> omega
  rw [h2101]
  constructor
  · -- Show 11 in the set
    use 191
    all_goals norm_num
  · -- Show there's no number less than 11 in the set
    intro x hx
    rcases hx with ⟨m, hx1, h_mod, hm_pos, h_eq⟩
    by_contra h3
    push_neg at h3
    interval_cases x <;> omega