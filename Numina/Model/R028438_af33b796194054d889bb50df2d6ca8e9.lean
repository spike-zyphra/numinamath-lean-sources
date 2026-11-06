import Mathlib

theorem number_theory_208181 (n : ℕ) (hn : n = 120) :
    IsLeast {x | ∃ k, x = (1 / (2 * (3 ^ (n - k)))) ^ k ∧ k ≤ n - 1} (1 / (2 * 3 ^ 39)) := by
  rw [hn]
  constructor
  · -- Show 1/(2 * 3^39) is in the set
    use 81
    all_goals
      norm_num
  · -- Show 1/(2 * 3^39) is the smallest
    intro x hx
    rcases hx with ⟨k, hk, hk_le⟩
    by_contra h
    push_neg at h
    have h1 : k ≤ 119 := by
      omega
    interval_cases k <;> norm_num at hk ⊢
    <;> omega