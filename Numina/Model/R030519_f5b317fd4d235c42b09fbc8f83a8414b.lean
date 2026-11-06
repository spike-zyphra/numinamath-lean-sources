import Mathlib

theorem number_theory_107370 :
    IsLeast {x | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ Nat.gcd a b = 2015 ∧ x = a + b ∧ (a + b) ∣ ((a - b)^2016 + b^2016)} 10075 := by 
  constructor
  · -- Show that 10075 is in the set with the pair (4030, 6045).
    use 4030, 6045
    all_goals norm_num
  · -- Show that 10075 is the least element in the set.
    intro x hx
    rcases hx with ⟨a, b, ha, hb, h1, hx, h2⟩
    by_contra h
    push_neg at h 
    have h3 : a + b < 10075 := by
      omega
    have h6 : a % 2015 = 0 := by
      have h7 : Nat.gcd a b = 2015 := h1
      have h8 : Nat.gcd a b ∣ a := by 
        apply Nat.gcd_dvd_left 
      have h9 : 2015 ∣ a := by 
        rw [h7] at h8 
        exact h8 
      exact Nat.dvd_iff_mod_eq_zero.mp h9 
    have h7 : b % 2015 = 0 := by
      have h7 : Nat.gcd a b = 2015 := h1
      have h8 : Nat.gcd a b ∣ b := by 
        apply Nat.gcd_dvd_right 
      have h9 : 2015 ∣ b := by 
        rw [h7] at h8 
        exact h8 
      exact Nat.dvd_iff_mod_eq_zero.mp h9
    have ha1 : ∃ k_a, a = 2015 * k_a := by 
      have : a % 2015 = 0 := h6 
      refine' ⟨a / 2015, by 
          omega 
        ⟩ 
    rcases ha1 with ⟨k_a, hka⟩ 
    have hb1 : ∃ k_b, b = 2015 * k_b := by 
      have : b % 2015 = 0 := h7 
      refine' ⟨b / 2015, by 
          omega 
        ⟩ 
    rcases hb1 with ⟨k_b, hkb⟩
    have h8 : k_a > 0 := by 
      by_contra h 
      push_neg at h 
      have : k_a = 0 := by 
        omega 
      rw [this] at hka 
      have : a = 0 := by 
        linarith 
      omega 
    have h9 : k_b > 0 := by 
      by_contra h 
      push_neg at h 
      have : k_b = 0 := by 
        omega 
      rw [this] at hkb 
      have : b = 0 := by 
        linarith 
      omega 
    have h10 : k_a + k_b < 5 := by 
      nlinarith [h3, hka, hkb]
    have h11 : k_a ≤ 4 := by 
      omega 
    have h12 : k_b ≤ 4 := by 
      omega 
    interval_cases k_a <;> interval_cases k_b 
      <;> norm_num [hka, hkb] at h1 h2 h3 ⊢
      <;> omega