import Mathlib

theorem number_theory_302376 :
    IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 2010 ∧ x = a + b + c} 78 := by
  constructor
  · -- Show that 78 is in the set using the triple (6, 5, 67)
    use 6, 5, 67
    all_goals norm_num
  · -- We need to show that x >= 78 for all x in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    by_contra h
    push_neg at h
    have h2 : a ∣ 2010 := by
      use b * c
      linarith
    have h3 : b ∣ 2010 := by
      use a * c
      linarith
    have h4 : c ∣ 2010 := by
      use a * b
      linarith
    have h5 : a ≤ 2010 := by
      exact Nat.le_of_dvd (by norm_num) h2
    have h6 : b ≤ 2010 := by
      exact Nat.le_of_dvd (by norm_num) h3
    have h7 : c ≤ 2010 := by
      exact Nat.le_of_dvd (by norm_num) h4
    have h8 : a + b + c < 78 := by linarith
    have h10 : a ≤ 77 := by
      omega
    have h11 : b ≤ 77 := by
      omega
    have h12 : c ≤ 77 := by
      omega
    interval_cases a <;> try { 
      omega
    } <;> try { 
      interval_cases b <;> omega
    }