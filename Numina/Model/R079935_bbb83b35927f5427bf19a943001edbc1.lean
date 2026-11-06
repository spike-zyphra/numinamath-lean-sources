import Mathlib

theorem number_theory_15344 (n : ℕ) (h₀ : n > 0) (h₁ : n < 1000000000) :
    IsGreatest {x | ∀ m, m > 0 → m < 10000 → x ∣ (m * 10001)} 10001 := by
  constructor
  · -- Show 10001 is in the set
    intro m h₂ h₃
    use m
    all_goals ring_nf at *
    all_goals try { omega }
  · -- Show that any x in the set is ≤ 10001
    intro x hx
    have h2 := hx 1 (by norm_num) (by norm_num)
    have h3 : x ∣ 10001 := by 
      simpa using h2
    have h4 : x ≤ 10001 := by 
      exact Nat.le_of_dvd (by norm_num) h3
    linarith