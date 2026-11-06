import Mathlib

theorem number_theory_301799 :
    IsLeast {x | ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ Nat.lcm a b = 12 ∧ Nat.lcm b c = 15 ∧ x = Nat.lcm a c} 20 := by
  constructor
  · -- Show 20 is in the set
    use 4, 3, 5
    all_goals norm_num [Nat.lcm]
  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, hx⟩
    have h3 : b ∣ 12 := by
      have h4 : b ∣ Nat.lcm a b := by
        exact Nat.dvd_lcm_right a b
      rw [h1] at h4
      exact h4
    have h4 : b ∣ 15 := by
      have h5 : b ∣ Nat.lcm b c := by
        exact Nat.dvd_lcm_left b c
      rw [h2] at h5
      exact h5
    have h5 : b ∣ 3 := Nat.dvd_gcd h3 h4
    have h6 : b = 1 ∨ b = 3 := by
      have h7 : b ≤ 3 := by
        exact Nat.le_of_dvd (show 0 < 3 by norm_num) h5
      interval_cases b <;> try tauto
    rcases h6 with (h7 | h7)
    · -- b = 1
      have h8 : a = 12 := by
        have h9 : Nat.lcm a b = 12 := h1
        rw [show b = 1 by omega] at h9
        have h10 : Nat.lcm a 1 = a := by
          simp [Nat.lcm]
        rw [h10] at h9
        linarith
      have h9 : c = 15 := by
        have h10 : Nat.lcm b c = 15 := h2
        rw [show b = 1 by omega] at h10
        have h11 : Nat.lcm 1 c = c := by
          simp [Nat.lcm]
        rw [h11] at h10
        linarith
      have hx2 : x = 60 := by
        rw [hx]
        rw [h8, h9]
        norm_num [Nat.lcm]
      have hx3 : x ≥ 20 := by
        omega
      linarith
    · -- b = 3
      have h7' : b = 3 := h7
      have h8 : a = 4 ∨ a = 12 := by
        have h10 : Nat.lcm a b = 12 := h1
        rw [show b = 3 by omega] at h10
        have h11 : a ∣ 12 := by
          have h17 : a ∣ Nat.lcm a 3 := by
            exact Nat.dvd_lcm_left a 3
          rw [h10] at h17
          exact h17
        have h18 : a ≤ 12 := by
          exact Nat.le_of_dvd (show 0 < 12 by norm_num) h11
        interval_cases a <;> norm_num [Nat.lcm] at h10 ⊢ <;> tauto
      have h9 : c = 5 ∨ c = 15 := by
        have h12 : Nat.lcm b c = 15 := h2
        rw [show b = 3 by omega] at h12
        have h13 : c ∣ 15 := by
          have h18 : c ∣ Nat.lcm 3 c := by
            exact Nat.dvd_lcm_right 3 c
          rw [h12] at h18
          exact h18
        have h18 : c ≤ 15 := by
          exact Nat.le_of_dvd (show 0 < 15 by norm_num) h13
        interval_cases c <;> norm_num [Nat.lcm] at h12 ⊢ <;> tauto
      rcases h8 with (ha' | ha')
      · -- a = 4
        rcases h9 with (hc' | hc')
        · -- c = 5
          have hx2 : x = 20 := by
            rw [hx]
            rw [ha', hc']
            norm_num [Nat.lcm]
          omega
        · -- c = 15
          have hx2 : x = 60 := by
            rw [hx]
            rw [ha', hc']
            norm_num [Nat.lcm]
          omega
      · -- a = 12
        rcases h9 with (hc' | hc')
        · -- c = 5
          have hx2 : x = 60 := by
            rw [hx]
            rw [ha', hc']
            norm_num [Nat.lcm]
          omega
        · -- c = 15
          have hx2 : x = 60 := by
            rw [hx]
            rw [ha', hc']
            norm_num [Nat.lcm]
          omega