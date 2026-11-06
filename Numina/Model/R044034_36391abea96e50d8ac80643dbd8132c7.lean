import Mathlib

theorem number_theory_103988 (a : ℕ) :
    (a^2 + a + 1) ∣ (a^7 + 3 * a^6 + 3 * a^5 + 3 * a^4 + a^3 + a^2 + 3) ↔
    a = 0 ∨ a = 1 := by 
  constructor
  · -- Assume (a^2 + a + 1) ∣ (a^7 + 3 * a^6 + 3 * a^5 + 3 * a^4 + a^3 + a^2 + 3), prove a = 0 ∨ a = 1
    intro h
    have h1 : (a ^ 2 + a + 1) ∣ (a ^ 7 + 3 * a ^ 6 + 3 * a ^ 5 + 3 * a ^ 4 + a ^ 3 + a ^ 2 + 3) := h
    have h2 : (a ^ 2 + a + 1) ∣ 3 := by 
      have h3 : (a ^ 2 + a + 1) ∣ (a ^ 7 + 3 * a ^ 6 + 3 * a ^ 5 + 3 * a ^ 4 + a ^ 3 + a ^ 2 + 3) := h1 
      have h4 : (a ^ 2 + a + 1) ∣ ( (a ^ 2 + a + 1) * (a^5 + 2 * a^4 + a ^ 2) ) := by 
        apply dvd_mul_right 
      have h5 : (a ^ 2 + a + 1) ∣ ((a ^ 7 + 3 * a ^ 6 + 3 * a ^ 5 + 3 * a ^ 4 + a ^ 3 + a ^ 2 + 3) - ( (a ^ 2 + a + 1) * (a^5 + 2 * a^4 + a ^ 2) )) := by 
        apply Nat.dvd_sub' 
        · exact h3 
        · exact h4 
      have h6 : ((a ^ 7 + 3 * a ^ 6 + 3 * a ^ 5 + 3 * a ^ 4 + a ^ 3 + a ^ 2 + 3) - ( (a ^ 2 + a + 1) * (a^5 + 2 * a^4 + a ^ 2) )) = 3 := by 
        ring_nf 
        <;> omega 
      rw [h6] at h5 
      exact h5 
    have h3 : (a ^ 2 + a + 1) ∣ 3 := h2 
    have h4 : (a ^ 2 + a + 1) ≤ 3 := by 
      exact Nat.le_of_dvd (show 0 < 3 by norm_num) h3 
    have h5 : a ≤ 1 := by 
      by_contra h 
      push_neg at h 
      have h6 : a ≥ 2 := by omega 
      nlinarith 
    interval_cases a <;> omega 
  · -- Assume a = 0 ∨ a = 1, prove (a^2 + a + 1) ∣ (a^7 + 3 * a^6 + 3 * a^5 + 3 * a^4 + a^3 + a^2 + 3)
    rintro (ha | ha)
    · -- Case a = 0
      rw [ha]
      all_goals norm_num 
    · -- Case a = 1
      rw [ha]
      all_goals norm_num