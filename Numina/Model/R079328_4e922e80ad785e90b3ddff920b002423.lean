import Mathlib

theorem number_theory_285981 :
    IsLeast {x | ∃ a b : ℕ, a * b = 24 ∧ x = a + b} 10 := by
  constructor
  · -- Show that 10 is in the set
    use 4, 6
    all_goals simp
  · -- Show that 10 is the least in the set
    intro x hx
    rcases hx with ⟨a, b, hprod, heq⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 24 := by
      by_contra h2
      push_neg at h2
      have h2' : a > 24 := by linarith
      have h3 : b < 1 := by
        nlinarith
      have h4 : b < 1 := by linarith
      nlinarith
      all_goals nlinarith
    have h2 : b ≤ 24 := by
      by_contra h2
      push_neg at h2
      have h2' : b > 24 := by linarith
      have h3 : a < 1 := by
        nlinarith
      have h4 : a < 1 := by linarith
      nlinarith
      all_goals nlinarith
    interval_cases a <;> interval_cases b
    <;> omega
    all_goals omega