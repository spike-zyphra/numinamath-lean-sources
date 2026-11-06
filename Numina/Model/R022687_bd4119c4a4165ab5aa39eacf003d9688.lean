import Mathlib

theorem number_theory_236839 :
    IsLeast {K : ℕ | 0 < K ∧ ∃ n, (8000 * K) = n ^ 2} 5 := by
  constructor
  · -- Show 5 is in the set.
    constructor
    · norm_num
    · -- Show that 8000 * 5 is a perfect square.
      use 200
      all_goals norm_num
  · -- Show that 5 is minimal.
    intro K h
    rcases h with ⟨hK_pos, ⟨n, hn⟩⟩
    by_contra h'
    push_neg at h'
    have h1 : K < 5 := by linarith
    have h2 : K = 1 ∨ K = 2 ∨ K = 3 ∨ K = 4 := by
      have h1 : K < 5 := by linarith
      have h3 : K > 0 := hK_pos
      interval_cases K <;> omega
    rcases h2 with (rfl | rfl | rfl | rfl)
    · -- Show that 8000 * 1 is not a perfect square.
      exfalso
      have h3 : n ≤ 90 := by nlinarith
      interval_cases n <;> omega
    · -- Show that 8000 * 2 is not a perfect square.
      exfalso
      have h3 : n ≤ 130 := by nlinarith
      interval_cases n <;> omega
    · -- Show that 8000 * 3 is not a perfect square.
      exfalso
      have h3 : n ≤ 155 := by nlinarith
      interval_cases n <;> omega
    · -- Show that 8000 * 4 is not a perfect square.
      exfalso
      have h3 : n ≤ 180 := by nlinarith
      interval_cases n <;> omega