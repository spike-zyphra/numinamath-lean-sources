import Mathlib

theorem number_theory_98508 :
    IsLeast {x | ∃ a b c : ℕ, x = Nat.lcm a c ∧ Nat.lcm a b = 12 ∧ Nat.lcm b c = 15} 20 := by 
  constructor 
  · -- Show 20 is in the set.
    use 4, 3, 5
    all_goals norm_num [Nat.lcm]
  · -- Show that 20 is the least in the set.
    intro x hx
    rcases hx with ⟨a, b, c, hx1, h1, h2⟩
    by_contra h
    push_neg at h
    rw [hx1] at h
    have h3 : Nat.lcm a c < 20 := h
    have h4 : b ∣ 12 := by
      have h5 : b ∣ Nat.lcm a b := by
        exact Nat.dvd_lcm_right a b
      rw [h1] at h5
      exact h5
    have h5 : b ∣ 15 := by
      have h6 : b ∣ Nat.lcm b c := by
        exact Nat.dvd_lcm_left b c
      rw [h2] at h6
      exact h6
    have h6 : b ∣ 3 := by
      exact Nat.dvd_gcd h4 h5
    have h7 : b = 1 ∨ b = 3 := by 
      have h8 : b ≤ 3 := by 
        exact Nat.le_of_dvd (by norm_num) h6
      interval_cases b <;> try { tauto }
    rcases h7 with (hb1 | hb3)
    · -- Case where b = 1
      have ha : a = 12 := by
        rw [hb1] at h1
        have h8 : Nat.lcm a 1 = 12 := h1
        simp at h8 
        linarith
      have hc : c = 15 := by
        rw [hb1] at h2
        have h9 : Nat.lcm 1 c = 15 := h2
        simp at h9 
        linarith
      rw [ha, hc] at h3
      norm_num [Nat.lcm] at h3 
    · -- Case where b = 3
      have h3' : Nat.lcm a 3 = 12 := by
        rw [hb3] at h1
        simpa using h1
      have h4' : Nat.lcm 3 c = 15 := by
        rw [hb3] at h2
        simpa using h2
      have hc1 : c = 5 ∨ c = 15 := by
        have h4 : Nat.lcm 3 c = 15 := h4'
        have h8 : c ∣ 15 := by 
          have h10 : c ∣ Nat.lcm 3 c := by 
            exact Nat.dvd_lcm_right 3 c 
          rw [h4] at h10 
          exact h10 
        have h15 : c ∣ 15 := h8 
        have h16 : c ≤ 15 := by 
          exact Nat.le_of_dvd (by norm_num) h15 
        interval_cases c <;> norm_num [Nat.lcm] at h4 <;> omega 
      have ha1 : a = 4 ∨ a = 12 := by 
        have h2' : Nat.lcm a 3 = 12 := h3'
        have h13 : a ∣ 12 := by 
          have h14 : a ∣ Nat.lcm a 3 := by 
            exact Nat.dvd_lcm_left a 3 
          rw [h2'] at h14 
          exact h14 
        have h15 : a ∣ 12 := h13 
        have h16 : a ≤ 12 := by 
          exact Nat.le_of_dvd (by norm_num) h15 
        interval_cases a <;> norm_num [Nat.lcm] at h2' <;> omega 
      rcases hc1 with (hc5 | hc15)
      · -- Case where c = 5
        rcases ha1 with (ha4 | ha12)
        · -- Case a = 4
          rw [ha4, hc5] at h3 
          norm_num [Nat.lcm] at h3 
        · -- Case a = 12
          rw [ha12, hc5] at h3 
          norm_num [Nat.lcm] at h3 
      · -- Case where c = 15
        rcases ha1 with (ha4 | ha12)
        · -- Case a = 4
          rw [ha4, hc15] at h3 
          norm_num [Nat.lcm] at h3 
        · -- Case a = 12
          rw [ha12, hc15] at h3 
          norm_num [Nat.lcm] at h3