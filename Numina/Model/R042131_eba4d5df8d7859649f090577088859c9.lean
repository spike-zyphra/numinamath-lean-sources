import Mathlib

theorem algebra_96609 (n : ℕ) (h : n = 2) :
    IsLeast {k | ∃ m, m > 500 ∧ n ^ 2 ^ k = m} 4 := by 
  rw [h]
  constructor
  · -- Show that 4 is in the set.
    use 65536
    all_goals
      norm_num
  · -- Show that 4 is the least element in the set.
    intro k hk
    rcases hk with ⟨m, hm1, hm2⟩
    by_contra h'
    push_neg at h'
    have h1 : k < 4 := by linarith
    have h2 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
      omega
    rcases h2 with (rfl | rfl | rfl | rfl)
    · -- k = 0
      norm_num [Nat.pow_succ, Nat.pow_zero] at hm2
      all_goals
        omega
    · -- k = 1
      norm_num [Nat.pow_succ, Nat.pow_zero] at hm2
      all_goals
        omega
    · -- k = 2
      norm_num [Nat.pow_succ, Nat.pow_zero] at hm2
      all_goals
        omega
    · -- k = 3
      norm_num [Nat.pow_succ, Nat.pow_zero] at hm2
      all_goals
        omega