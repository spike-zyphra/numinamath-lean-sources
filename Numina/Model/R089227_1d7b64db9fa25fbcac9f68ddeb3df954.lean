import Mathlib

theorem number_theory_272792 : IsGreatest {k | 0 < k ∧ (6 ^ k : ℤ) ∣ 8 * 48 * 81} 5 := by 
  constructor 
  · -- Show that 5 ∈ {k | 0 < k ∧ (6 ^ k : ℤ) ∣ 8 * 48 * 81}
    constructor
    · -- Show 5 > 0 
      norm_num
    · -- Show 6^5 divides 8 * 48 * 81 
      norm_num 
  · -- Show that for all k ∈ {k | 0 < k ∧ (6 ^ k : ℤ) ∣ 8 * 48 * 81}, k ≤ 5
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩ 
    by_contra h 
    push_neg at h 
    have h6 : k ≥ 6 := by linarith 
    have h7 : (6 : ℤ) ^ 6 > 8 * 48 * 81 := by 
      norm_num 
    have h8 : (6 : ℤ) ^ k > 8 * 48 * 81 := by 
      have h9 : k ≥ 6 := h6 
      have h10 : (6 : ℤ) ^ k ≥ (6 : ℤ) ^ 6 := by 
        exact pow_le_pow_right (by norm_num) h9 
      have h11 : (6 : ℤ) ^ 6 > 8 * 48 * 81 := h7 
      linarith 
    have h12 : (6 : ℤ) ^ k ≤ (8 * 48 * 81 : ℤ) := by 
      exact Int.le_of_dvd (by norm_num) hk_div 
    linarith