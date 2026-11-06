import Mathlib

theorem number_theory_7143 :
    IsGreatest {a : ℕ | ∃ b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ Nat.factorial a * Nat.factorial b * Nat.factorial c = 25920} 6 := by
  constructor
  · -- Show $6$ is in the set.
    use 3, 3
    repeat { constructor }
    all_goals norm_num [Nat.factorial]
  · -- Show $6$ is greatest.
    intro a ha
    rcases ha with ⟨b, c, ha_pos, hb_pos, hc_pos, heq⟩
    by_contra h
    push_neg at h
    have h1 : a ≥ 7 := by omega 
    have h2 : 7 ∣ Nat.factorial a := by 
      have h3 : a ≥ 7 := by omega 
      have : 7 ∣ Nat.factorial a := by 
        apply Nat.dvd_factorial
        all_goals omega 
      assumption 
    have h3 : 7 ∣ Nat.factorial a * Nat.factorial b * Nat.factorial c := by 
      have h4 : 7 ∣ Nat.factorial a := h2 
      have : 7 ∣ Nat.factorial a * Nat.factorial b * Nat.factorial c := by 
        have h5 : 7 ∣ Nat.factorial a := h4 
        have h6 : Nat.factorial a * Nat.factorial b * Nat.factorial c = (Nat.factorial a) * (Nat.factorial b * Nat.factorial c) := by ring 
        rw [h6]
        have h7 : 7 ∣ (Nat.factorial a) := h4 
        have h8 : 7 ∣ (Nat.factorial a) * (Nat.factorial b * Nat.factorial c) := by 
          apply dvd_trans h7 
          apply dvd_mul_right 
        assumption 
      assumption 
    have h4 : 7 ∣ (25920 : ℕ) := by 
      have h5 : Nat.factorial a * Nat.factorial b * Nat.factorial c = 25920 := by linarith [heq]
      have h6 : 7 ∣ Nat.factorial a * Nat.factorial b * Nat.factorial c := h3 
      rw [h5] at h6 
      exact h6 
    norm_num at h4