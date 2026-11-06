import Mathlib

theorem number_theory_96803 :
    IsGreatest {x | ∃ n m : ℕ, n * m = 36 ∧ x = n + m} 37 := by
  constructor
  · -- Show that 37 belongs to the set
    use 1, 36
    all_goals trivial
  · -- Show that 37 is greatest in the set
    intro x hx
    rcases hx with ⟨n, m, hprod, heq⟩
    have h1 : n * m = 36 := hprod
    have h2 : n ≤ 36 := by
      by_contra h
      push_neg at h
      have h3 : m < 1 := by
        nlinarith
      have h4 : m = 0 := by linarith
      rw [h4] at hprod
      nlinarith
    interval_cases n <;> omega