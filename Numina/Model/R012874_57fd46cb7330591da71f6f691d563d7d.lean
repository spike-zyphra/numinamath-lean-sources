import Mathlib

theorem number_theory_165448 (a b c : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (h : a * b + b * c = 119) : a + b + c = 24 := by
  have h1 : b ∣ 119 := by
    use a + c
    linarith
  have h2 : b = 7 ∨ b = 17 := by
    have h3 : b ≤ 119 := by 
      exact Nat.le_of_dvd (by norm_num) h1
    interval_cases b <;> norm_num at h1 hb ⊢ 
  rcases h2 with (hb_eq | hb_eq)
  · -- if b = 7
    have h_eq : a + c = 17 := by
      rw [hb_eq] at h
      nlinarith
    have h3 : a ≤ 17 := by
      omega
    have h4 : c ≤ 17 := by
      omega
    interval_cases a <;> interval_cases c 
      <;> norm_num at h_eq ha hc 
  · -- if b = 17
    have h_eq : a + c = 7 := by
      rw [hb_eq] at h
      nlinarith
    have h3 : a ≤ 7 := by
      omega
    have h4 : c ≤ 7 := by
      omega
    interval_cases a <;> interval_cases c 
      <;> norm_num at h_eq ha hc 
      <;> omega