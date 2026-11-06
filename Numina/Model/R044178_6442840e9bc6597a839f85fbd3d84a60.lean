import Mathlib

theorem number_theory_15128 : IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ Nat.gcd a b = 168 ∧ Nat.gcd a c = 693 ∧ x = Nat.gcd b c} 21 := by
  constructor
  · -- Show that 21 is in the set
    use 5544, 168, 693
    all_goals norm_num [Nat.gcd]
  · -- Show that 21 is minimal
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : Nat.gcd a b = 168 := h1
    have h5 : Nat.gcd a c = 693 := h2
    have h6 : x = Nat.gcd b c := h3
    -- Show that 21 divides gcd b c
    have h7 : 21 ∣ Nat.gcd b c := by
      have h8 : 21 ∣ Nat.gcd a b := by
        rw [h4]
        all_goals norm_num
      have h9 : 21 ∣ Nat.gcd a c := by
        rw [h5]
        all_goals norm_num
      -- Show that 21 divides a
      have h10 : 21 ∣ a := by
        have h8' : 21 ∣ Nat.gcd a b := h8
        have h11 : Nat.gcd a b ∣ a := by
          exact Nat.gcd_dvd_left a b
        have h12 : 21 ∣ a := by
          exact dvd_trans h8' h11
        exact h12
      -- Show that 21 divides b
      have h14 : 21 ∣ b := by
        have h8' : 21 ∣ Nat.gcd a b := h8
        have h15 : Nat.gcd a b ∣ b := by
          exact Nat.gcd_dvd_right a b
        have h16 : 21 ∣ b := by
          exact dvd_trans h8' h15
        exact h16
      -- Show that 21 divides c
      have h17 : 21 ∣ c := by
        have h9' : 21 ∣ Nat.gcd a c := h9
        have h18 : Nat.gcd a c ∣ c := by
          exact Nat.gcd_dvd_right a c
        have h19 : 21 ∣ c := by
          exact dvd_trans h9' h18
        exact h19
      -- Show that 21 divides gcd b c
      have h18 : 21 ∣ Nat.gcd b c := by
        apply Nat.dvd_gcd
        · exact h14
        · exact h17
      exact h18
    -- Show that gcd b c ≥ 21
    have h8 : 21 ∣ x := by
      rw [show x = Nat.gcd b c by linarith [h6]]
      exact h7
    have h9 : x < 21 := h
    have h10 : x > 0 := by
      rw [show x = Nat.gcd b c by linarith [h6]]
      apply Nat.gcd_pos_of_pos_left
      exact hb
    interval_cases x <;> omega