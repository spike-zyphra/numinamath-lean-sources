import Mathlib

theorem algebra_63966 : IsLeast {z | ∃(a b : ℤ), 0 < a ∧ 0 < b ∧ a * b - 7 * a - 11 * b + 13 = 0 ∧ z = a + b} 34 := by
  constructor
  · -- Show 34 is achievable with a = 19, b = 15
    use 19, 15
    all_goals norm_num
  · -- Show 34 is the least such value
    intro z h
    rcases h with ⟨a, b, ha, hb, heq, hz⟩
    by_contra h'
    push_neg at h'
    have h1 : a + b < (34 : ℤ) := by
      omega
    have h2 : a ≤ (32 : ℤ) := by
      omega
    have h3 : b ≤ (32 : ℤ) := by
      omega
    interval_cases a <;> interval_cases b
    <;> omega