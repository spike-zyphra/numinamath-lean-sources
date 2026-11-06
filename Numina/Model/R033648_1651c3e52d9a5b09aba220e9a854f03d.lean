import Mathlib

theorem algebra_112578 (k : ℤ) :
    (k - 1) ∣ (2 * k ^ 2 + k - 8) ↔ k = 6 ∨ k = 2 ∨ k = 0 ∨ k = -4 := by 
  constructor
  · -- Assume that k - 1 divides 2k^2 + k - 8, then prove k = 6 ∨ k = 2 ∨ k = 0 ∨ k = -4
    intro h
    have h1 : (k - 1) ∣ (2 * k ^ 2 + k - 8) := h
    have h2 : (k - 1) ∣ 5 := by
      have h3 : (k - 1) ∣ (2 * k ^ 2 + k - 8) := h1
      have h4 : (k - 1) ∣ (k - 1) * (2 * k + 3) := by
        apply dvd_mul_right
      have h5 : (k - 1) ∣ ((k - 1) * (2 * k + 3) - (2 * k ^ 2 + k - 8)) := by
        apply Dvd.dvd.sub
        · exact h4
        · exact h3
      have h6 : ((k - 1) * (2 * k + 3) - (2 * k ^ 2 + k - 8)) = 5 := by
        ring
      have h7 : (k - 1) ∣ 5 := by 
        rw [h6] at h5
        exact h5
      exact h7
    have h3 : k - 1 ∣ 5 := h2
    have h4 : k - 1 ≤ 5 := by 
      apply Int.le_of_dvd (show 0 < 5 by norm_num) h3 
    have h5 : k - 1 ≥ -5 := by 
      have h5 : -(k - 1) ∣ 5 := by 
        exact Int.neg_dvd.2 h3 
      have h6 : -(k - 1) ≤ 5 := by 
        apply Int.le_of_dvd (show 0 < 5 by norm_num) h5 
      have h7 : k - 1 ≥ -5 := by 
        linarith 
      exact h7 
    have h8 : k ≤ 6 := by 
      linarith 
    have h9 : k ≥ -4 := by 
      linarith 
    have h10 : k = 6 ∨ k = 2 ∨ k = 0 ∨ k = -4 := by 
      interval_cases k <;> try { tauto } 
    exact h10
  · -- Assume k = 6 ∨ k = 2 ∨ k = 0 ∨ k = -4, then prove (k - 1) ∣ (2 * k ^ 2 + k - 8)
    rintro (h | h | h | h)
    · -- Case k = 6 
      rw [show k = 6 by linarith]
      all_goals 
        norm_num 
    · -- Case k = 2 
      rw [show k = 2 by linarith]
      all_goals 
        norm_num 
    · -- Case k = 0 
      rw [show k = 0 by linarith]
      all_goals 
        norm_num 
    · -- Case k = -4 
      rw [show k = -4 by linarith]
      all_goals 
        norm_num