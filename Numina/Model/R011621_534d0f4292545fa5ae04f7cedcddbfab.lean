import Mathlib

theorem number_theory (a b c : ℕ) (h: a*b*c = 21) (aneb : a ≠ b) (anec : a ≠ c) (bnec : b ≠ c) : a + b + c = 11 := by
  have absac1 : a ∣ 21 := by
    use b * c
    all_goals nlinarith
  have absbc1 : b ∣ 21 := by
    use a * c
    all_goals nlinarith
  have abscc1 : c ∣ 21 := by
    use a * b
    all_goals nlinarith
  have h7 : a ≤ 21 := by
    exact Nat.le_of_dvd (by norm_num) absac1
  have h8 : b ≤ 21 := by
    exact Nat.le_of_dvd (by norm_num) absbc1
  have h9 : c ≤ 21 := by
    exact Nat.le_of_dvd (by norm_num) abscc1
  interval_cases a <;> 
    try {
      omega
    }
  <;> interval_cases b 
  <;> omega