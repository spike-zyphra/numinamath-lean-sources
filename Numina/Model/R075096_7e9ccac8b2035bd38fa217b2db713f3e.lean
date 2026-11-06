import Mathlib

theorem number_theory_234998 :
    IsGreatest {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a * b * c = 24 ∧ x = a + b + c} 15 := by
  constructor
  · -- Show 15 is achievable
    use 1, 2, 12
    all_goals norm_num
  · -- Show 15 is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hneq1, hneq2, hneq3, hprod, hx⟩
    by_contra h
    push_neg at h
    have h1 : a ≤ 24 := by
      have : a * b * c = 24 := hprod
      have h2 : b * c ≥ 1 := by nlinarith
      have : a ≤ 24 := by nlinarith
      omega
    have h2 : b ≤ 24 := by
      have : a * b * c = 24 := hprod
      have h2 : a * c ≥ 1 := by nlinarith
      have : b ≤ 24 := by nlinarith
      omega
    have h3 : c ≤ 24 := by
      have : a * b * c = 24 := hprod
      have h2 : a * b ≥ 1 := by nlinarith
      have : c ≤ 24 := by nlinarith
      omega
    interval_cases a <;> interval_cases b <;> omega