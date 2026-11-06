import Mathlib

theorem number_theory_11609 : IsGreatest {m : ℕ | ∃ n : ℕ, m = n * (n % 10) ∧ 10 ≤ n ∧ n ≤ 99 ∧ m % 10 = n % 10 ∧ n / 10 = n % 10} 396 := by
  constructor
  · -- Show that 396 is in the set.
    use 66
    all_goals norm_num
  · -- Show that 396 is the greatest.
    intro m hm
    rcases hm with ⟨n, h1, h2, h3, h4, h5⟩
    interval_cases n <;> norm_num [h1] at h4 ⊢ <;> omega