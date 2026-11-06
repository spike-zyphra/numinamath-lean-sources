import Mathlib

theorem number_theory_100578 :
    IsLeast {x | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ Nat.lcm a b = 12 ∧ Nat.lcm b c = 15 ∧ x = Nat.lcm a c} 20 := by
  constructor
  · -- Show 20 is in the set
    use 4, 3, 5
    all_goals norm_num [Nat.lcm]
  · -- Show that 20 is the least
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : a ∣ Nat.lcm a b := by
      apply Nat.dvd_lcm_left
    have h5 : b ∣ Nat.lcm a b := by
      apply Nat.dvd_lcm_right
    rw [h1] at h4 h5
    have h6 : b ∣ Nat.lcm b c := by
      apply Nat.dvd_lcm_left
    have h7 : c ∣ Nat.lcm b c := by
      apply Nat.dvd_lcm_right
    rw [h2] at h6 h7
    have h8 : b = 1 ∨ b = 3 := by 
      have h9 : b ∣ 12 := by
        exact h5
      have h10 : b ∣ 15 := by
        exact h6
      have h11 : b ∣ 3 := by
        exact Nat.dvd_gcd h9 h10
      have h12 : b = 1 ∨ b = 3 := by
        have h13 : b ≤ 3 := by
          exact Nat.le_of_dvd (by norm_num) h11
        interval_cases b <;> try { tauto }
      tauto
    rcases h8 with (h8 | h8)
    · -- Case b = 1
      have h10 : a = 12 := by
        rw [h8] at h1
        simp [Nat.lcm] at h1
        all_goals omega
      have h11 : c = 15 := by
        rw [h8] at h2
        simp [Nat.lcm] at h2
        all_goals omega
      have h12 : Nat.lcm a c = 60 := by
        rw [h10, h11]
        all_goals norm_num [Nat.lcm]
      have h13 : x = 60 := by
        linarith [h3, h12]
      omega
    · -- Case b = 3
      have h14 : a = 4 ∨ a = 12 := by
        have h15 : Nat.lcm a 3 = 12 := by
          rw [h8] at h1
          exact_mod_cast h1
        have h16 : a ∣ 12 := by
          have h17 : a ∣ Nat.lcm a 3 := by
            apply Nat.dvd_lcm_left
          rw [h15] at h17
          exact h17
        have h17 : a ≤ 12 := by
          exact Nat.le_of_dvd (by norm_num) h16
        interval_cases a <;> norm_num [Nat.lcm] at h15 ⊢
        <;> tauto
      have h18 : c = 5 ∨ c = 15 := by
        have h19 : Nat.lcm 3 c = 15 := by
          rw [h8] at h2
          exact_mod_cast h2
        have h20 : c ∣ 15 := by
          have h21 : c ∣ Nat.lcm 3 c := by
            apply Nat.dvd_lcm_right
          rw [h19] at h21
          exact h21
        have h21 : c ≤ 15 := by
          exact Nat.le_of_dvd (by norm_num) h20
        interval_cases c <;> norm_num [Nat.lcm] at h19 ⊢
        <;> tauto
      rcases h14 with (h14 | h14)
      · -- Case a = 4
        rcases h18 with (h18 | h18)
        · -- Case c = 5
          have h9 : Nat.lcm a c = 20 := by
            rw [h14, h18]
            all_goals norm_num [Nat.lcm]
          omega
        · -- Case c = 15
          have h9 : Nat.lcm a c = 60 := by
            rw [h14, h18]
            all_goals norm_num [Nat.lcm]
          omega
      · -- Case a = 12
        rcases h18 with (h18 | h18)
        · -- Case c = 5
          have h9 : Nat.lcm a c = 60 := by
            rw [h14, h18]
            all_goals norm_num [Nat.lcm]
          omega
        · -- Case c = 15
          have h9 : Nat.lcm a c = 60 := by
            rw [h14, h18]
            all_goals norm_num [Nat.lcm]
          omega