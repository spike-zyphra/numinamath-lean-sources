import Mathlib

theorem number_theory_13190 : IsGreatest { x : ℕ | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ a + b = 1001 ∧ x = a.gcd b } 143 := by
  constructor
  · -- Show 143 is in the set
    use 429, 572
    all_goals norm_num
  · -- Show no greater element is in the set
    intro x h
    rcases h with ⟨a, b, ha, hb, h1, hx⟩
    have h2 : a.gcd b ∣ a := by apply Nat.gcd_dvd_left
    have h3 : a.gcd b ∣ b := by apply Nat.gcd_dvd_right
    have h4 : a.gcd b ∣ a + b := by
      apply Nat.dvd_add
      · exact h2
      · exact h3
    have h5 : a.gcd b ∣ 1001 := by
      rw [show a + b = 1001 by linarith] at h4
      exact h4
    have h6 : a.gcd b ≤ 143 := by
      have h7 : a.gcd b ∣ 1001 := h5
      have h8 : a.gcd b ≤ 143 := by
        have h9 : a.gcd b ∣ 1001 := h7
        have h10 : a.gcd b ≤ 143 := by
          by_contra h
          push_neg at h
          have h13 : a.gcd b > 143 := h
          have h14 : a.gcd b ∣ 1001 := h9
          have h15 : a.gcd b ≤ 1001 := by 
            exact Nat.le_of_dvd (by linarith) h14
          interval_cases k : a.gcd b <;> norm_num at h14 h13 h15 ⊢
          <;> omega
        linarith
      linarith
    have h7 : x ≤ 143 := by 
      linarith [hx, h6]
    linarith