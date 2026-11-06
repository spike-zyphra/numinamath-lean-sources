import Mathlib

theorem number_theory_236674 :
    IsGreatest {x | ∃ r l c : ℕ, r * x = 252 ∧ l * x = 288 ∧ c * x = 972} 36 := by
  constructor
  · -- Show that 36 is in the set
    use 7, 8, 27
    all_goals norm_num
  · -- Show that 36 is the greatest in the set
    intro x hx
    rcases hx with ⟨r, l, c, hr, hl, hc⟩
    have h1 : x ∣ 252 := by 
      use r
      linarith
    have h2 : x ∣ 288 := by 
      use l
      linarith
    have h3 : x ∣ 972 := by 
      use c
      linarith
    have h4 : x ∣ Nat.gcd (Nat.gcd 252 288) 972 := Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3
    have h5 : Nat.gcd (Nat.gcd 252 288) 972 = 36 := by 
      norm_num [Nat.gcd]
    rw [h5] at h4
    have h6 : x ≤ 36 := by 
      exact Nat.le_of_dvd (by norm_num) h4
    linarith