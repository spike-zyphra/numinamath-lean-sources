import Mathlib

theorem number_theory_199919 :
    IsLeast {k | ∃ m n : ℕ, m > n ∧ k = m + n ∧ 70^2 ∣ 2023^m - 2023^n} 24 := by
  constructor
  · -- Show that 24 is in the set
    use 22, 2
    all_goals norm_num
  · -- Show that 24 is the least
    intro k hk
    rcases hk with ⟨m, n, hmn, hk_eq, hdiv⟩
    have h24 : k ≥ 24 := by
      by_contra h
      push_neg at h
      have hk1 : k < 24 := by linarith
      have h1 : m + n < 24 := by linarith [hk_eq, hk1]
      -- The pair (m, n) must satisfy m > n and m +n < 24
      have h2 : m < 24 := by
        omega
      have h3 : n < 24 := by
        omega
      interval_cases m <;> interval_cases n 
      <;> norm_num [hk_eq] at hdiv ⊢ 
      <;> omega
    linarith [hk_eq, h24]