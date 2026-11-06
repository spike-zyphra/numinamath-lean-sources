import Mathlib

theorem number_theory_19152 {p : ℕ → ℕ} (hp : p = fun n => n ^ 2 - n + 41) :
    IsLeast {n | 0 < n ∧ p n > 0 ∧ p (n + 1) > 0 ∧ Nat.gcd (p n) (p (n + 1)) > 1} 41 := by
  constructor
  · -- Show that 41 is in the set
    constructor
    · norm_num
    constructor
    · -- Show that p 41 > 0
      rw [hp]
      norm_num
    constructor
    · -- Show that p 42 > 0
      rw [hp]
      norm_num
    · -- Show that gcd (p 41) (p 42) > 1
      rw [hp]
      norm_num [Nat.gcd]
  · -- Show that no integer less than 41 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hp_n_pos, hp_n1_pos, h_gcd⟩
    by_contra h
    push_neg at h
    -- So h : n < 41
    have hp1 : p n = n ^ 2 - n + 41 := by simp [hp]
    have hp2 : p (n + 1) = (n + 1) ^ 2 - (n + 1) + 41 := by simp [hp]
    rw [hp1] at h_gcd hp_n_pos
    rw [hp2] at h_gcd hp_n1_pos
    interval_cases n <;> norm_num at hp_n_pos hp_n1_pos h_gcd ⊢
    all_goals try { contradiction }