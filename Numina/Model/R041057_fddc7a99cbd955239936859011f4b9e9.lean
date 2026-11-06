import Mathlib

theorem algebra_11130 :
    IsLeast {x : ℕ | ∃ a b : ℤ, a > 0 ∧ b > 0 ∧ a * b - 6 * a + 5 * b = 373 ∧ x = |a - b|} 31 := by
  constructor
  · -- Show that 31 is in the set
    use 44, 13
    all_goals norm_num
  · -- Show that 31 is the least
    intro x h
    rcases h with ⟨a, b, ha, hb, heq, hx⟩
    by_contra h'
    push_neg at h'
    have h2 : x ≤ 30 := by
      omega
    have h3 : |a - b| ≤ (30 : ℤ) := by
      omega
    have eq1 : a * b - 6 * a + 5 * b = (373 : ℤ) := heq
    have h6 : a ≤ 343 := by
      by_contra h
      push_neg at h
      have h7 : a + 5 > 343 := by
        omega
      have h8 : (a + 5) ∣ (343 : ℤ) := by
        have h11 : (a + 5) * (b - 6) = (343 : ℤ) := by
          nlinarith
        use b - 6
        all_goals linarith
      have h10 : (a + 5) ≤ (343 : ℤ) := by
        exact Int.le_of_dvd (by norm_num) h8
      linarith
    have h7 : b ≤ 349 := by
      nlinarith [show (a + 5) * (b - 6) = 343 from by nlinarith]
    have h8 : (a + 5) * (b - 6) = (343 : ℤ) := by 
      nlinarith
    have h4 : a - b ≤ 30 := by 
      cases' abs_le.mp (show |a - b| ≤ (30 : ℤ) by linarith) with h5 h6
      linarith
    have h5 : -30 ≤ a - b := by
      cases' abs_le.mp (show |a - b| ≤ (30 : ℤ) by linarith) with h5 h6
      linarith
    interval_cases a <;> omega