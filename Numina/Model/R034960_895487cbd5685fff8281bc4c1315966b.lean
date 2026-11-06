import Mathlib

theorem number_theory_69931 :
    IsGreatest {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + 2 * b + 3 * c = 100 ∧ x = a * b * c} 6171 := by 
  constructor
  · -- First, we prove that 6171 is achievable
    exact ⟨33, 17, 11, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Now we prove that 6171 is greatest
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : a ≤ 100 := by
      omega
    have h3 : b ≤ 50 := by 
      omega
    have h4 : c ≤ 33 := by
      omega
    have hx' : a * b * c ≤ 6171 := by 
      interval_cases c <;> interval_cases b <;> omega
    linarith [hx, hx']