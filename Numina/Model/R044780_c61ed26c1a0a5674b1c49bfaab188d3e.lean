import Mathlib

theorem number_theory_105820 (p : ℕ) (hp : p.Prime) :
    ∃ k, p^2 - p + 1 = k^3 ↔ p = 19 := by
  use 7
  constructor
  · -- Assume p^2 - p + 1 = 7^3, prove p = 19
    intro h
    have h1 : p ≤ 19 := by
      by_contra h2
      push_neg at h2
      have h_eq : p ^ 2 = p + 342 := by
        have h_eq1 : p ^ 2 - p + 1 = 343 := by
          omega
        omega
      have h4 : p ≥ 20 := by
        omega
      have h5 : p ^ 2 ≥ p + 380 := by
        nlinarith [show p ≥ 20 from h4]
      nlinarith [h_eq, h5]
    interval_cases p <;> norm_num at h <;> trivial
  · -- Assume p = 19, prove p^2 - p + 1 = 7^3
    intro hp_eq
    rw [hp_eq]
    all_goals norm_num