import Mathlib

theorem algebra_113441 (a : ℕ) :
    Nat.gcd (2 * a + 5) (3 * a + 4) ≠ 1 ↔ ∃ k, a = 7 * k + 1 := by
  constructor
  · -- Assume Nat.gcd (2 * a + 5) (3 * a + 4) ≠ 1, prove ∃ k, a = 7 * k + 1
    intro h
    have h1 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ 2 * a + 5 := by
      apply Nat.gcd_dvd_left
    have h2 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ 3 * a + 4 := by
      apply Nat.gcd_dvd_right
    have h3 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ 7 := by
      have h4 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ (3 * (2 * a + 5)) := by
        exact dvd_trans h1 (by norm_num)
      have h5 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ (2 * (3 * a + 4)) := by
        exact dvd_trans h2 (by norm_num)
      have h6 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ (3 * (2 * a + 5) - 2 * (3 * a + 4)) := by
        apply Nat.dvd_sub'
        · -- Show that Nat.gcd (2 * a + 5) (3 * a + 4) divides 3 * (2 * a + 5)
          exact h4
        · -- Show that Nat.gcd (2 * a + 5) (3 * a + 4) divides 2 * (3 * a + 4)
          exact h5
      have h7 : 3 * (2 * a + 5) - 2 * (3 * a + 4) = 7 := by
        omega
      rw [h7] at h6
      exact h6
    have h4 : Nat.gcd (2 * a + 5) (3 * a + 4) = 7 := by
      have h5 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ 7 := h3
      have h7 : Nat.gcd (2 * a + 5) (3 * a + 4) > 1 := by
        by_contra h
        push_neg at h
        have : Nat.gcd (2 * a + 5) (3 * a + 4) = 1 := by
          have h11 : Nat.gcd (2 * a + 5) (3 * a + 4) < 2 := by linarith
          interval_cases h' : Nat.gcd (2 * a + 5) (3 * a + 4) <;> try { tauto }
          all_goals omega
        omega
      have h8 : Nat.gcd (2 * a + 5) (3 * a + 4) ≤ 7 := by
        exact Nat.le_of_dvd (show 0 < 7 by norm_num) h5
      interval_cases h' : Nat.gcd (2 * a + 5) (3 * a + 4) <;> try { tauto }
      all_goals omega
    have h5 : (7 : ℕ) ∣ 2 * a + 5 := by
      have h7 : (7 : ℕ) ∣ 2 * a + 5 := by
        have h6 : Nat.gcd (2 * a + 5) (3 * a + 4) ∣ 2 * a + 5 := by
          apply Nat.gcd_dvd_left
        rw [show Nat.gcd (2 * a + 5) (3 * a + 4) = 7 by omega] at h6
        exact h6
      exact h7
    have h5 : a % 7 = 1 := by
      omega
    refine ⟨a / 7, by omega⟩
  · -- Assume ∃ k, a = 7 * k + 1, prove Nat.gcd (2 * a + 5) (3 * a + 4) ≠ 1
    rintro ⟨k, hk⟩
    have h1 : 2 * a + 5 = 7 * (2 * k + 1) := by
      rw [hk]
      all_goals
        ring_nf
        <;> omega
    have h2 : 3 * a + 4 = 7 * (3 * k + 1) := by
      rw [hk]
      all_goals
        ring_nf
        <;> omega
    rw [h1, h2]
    have h3 : Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) > 1 := by
      have h4 : Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) ≥ 7 := by
        have h5 : 7 ∣ Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) := by
          have h6 : 7 ∣ 7 * (2 * k + 1) := by
            omega
          have h7 : 7 ∣ 7 * (3 * k + 1) := by
            omega
          exact Nat.dvd_gcd h6 h7
        have h10 : 7 ∣ Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) := h5
        have h11 : Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) ≠ 0 := by 
          have h12 : 7 * (2 * k + 1) > 0 := by
            omega 
          have h13 : 7 * (3 * k + 1) > 0 := by
            omega 
          have h14 : Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) > 0 := by 
            apply Nat.gcd_pos_of_pos_left 
            all_goals linarith
          omega
        have h8 : Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) ≥ 7 := by
          omega
        exact h8
      omega
    have h4 : Nat.gcd (7 * (2 * k + 1)) (7 * (3 * k + 1)) ≠ 1 := by
      omega
    exact h4