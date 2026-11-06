import Mathlib

theorem number_theory_74949 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a * b = 2400 ∧ x = a + b} 98 := by
  constructor
  · -- Show 98 is in the set
    exact ⟨48, 50, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that no number less than 98 is in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hab, hx⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 96 := by
      omega
    have h2 : b ≤ 96 := by
      omega
    interval_cases a <;> omega