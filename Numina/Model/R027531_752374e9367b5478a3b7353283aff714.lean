import Mathlib

theorem number_theory_36535 {a b : ℤ} (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : b^2 + a * b + 1 ∣ a^2 + a * b + 1) : a = b := by 
  have h4 : b^2 + a * b + 1 ∣ a^2 - b^2 := by 
    have h5 : b^2 + a * b + 1 ∣ (a^2 + a * b + 1) := h₁ 
    have h6 : b^2 + a * b + 1 ∣ (b^2 + a * b + 1) := by 
      simp 
    have h7 : b^2 + a * b + 1 ∣ ((a^2 + a * b + 1) - (b^2 + a * b + 1)) := by 
      apply Dvd.dvd.sub h5 h6 
    have h8 : (a^2 + a * b + 1) - (b^2 + a * b + 1) = a^2 - b^2 := by 
      ring 
    rw [h8] at h7 
    exact h7 
  have h5 : IsCoprime (b^2 + a * b + 1) (a + b) := by
    use 1 
    use -b 
    ring
  have h2 : b^2 + a * b + 1 ∣ a - b := by 
    have h3 : b^2 + a * b + 1 ∣ a^2 - b^2 := h4 
    have h4 : IsCoprime (b^2 + a * b + 1) (a + b) := h5 
    have h6 : b^2 + a * b + 1 ∣ (a - b) * (a + b) := by 
      have h7 : (a - b) * (a + b) = a^2 - b^2 := by 
        ring 
      rw [h7] 
      exact h3 
    have h7 : b^2 + a * b + 1 ∣ (a - b) := by 
      have h10 : IsCoprime (b^2 + a * b + 1) (a + b) := h4 
      have h11 : b^2 + a * b + 1 ∣ (a + b) * (a - b) := by 
        have h7 : b^2 + a * b + 1 ∣ (a - b) * (a + b) := h6 
        have h8 : (a - b) * (a + b) = (a + b) * (a - b) := by 
          ring 
        rw [h8] at h7 
        exact h7 
      have h12 : b^2 + a * b + 1 ∣ (a - b) := by 
        apply IsCoprime.dvd_of_dvd_mul_left h10 h11 
      exact h12 
    exact h7 
  obtain ⟨k, hk⟩ := h2 
  have h6 : (a - b) = 0 := by 
    by_cases h7 : k > 0 
    · -- Assume k >0, so k≥1 
      have hk1 : k ≥ 1 := by 
        omega 
      have h7a : b^2 + a * b + 1 > 0 := by 
        nlinarith [sq_pos_of_pos (show (a : ℤ) > 0 by linarith), sq_pos_of_pos (show (b : ℤ) > 0 by linarith)]
      have h7b : a - b ≥ b^2 + a * b + 1 := by 
        nlinarith [hk, sq_nonneg (k : ℤ), show k ≥ 1 by omega, sq_nonneg ((b : ℤ) ^ 2 + (a * b : ℤ) + 1 : ℤ)]
      nlinarith [mul_pos (show 0 < a by linarith) (show 0 < b by linarith), sq_nonneg (b : ℤ), sq_nonneg (a - b : ℤ), sq_pos_of_pos (show (a : ℤ) > 0 by linarith), sq_pos_of_pos (show (b : ℤ) > 0 by linarith)]
    by_cases h8 : k < 0 
    · -- Assume k <0, so k ≤ -1 
      have hk1 : k ≤ -1 := by 
        omega 
      have h7a : b^2 + a * b + 1 > 0 := by 
        nlinarith [sq_pos_of_pos (show (a : ℤ) > 0 by linarith), sq_pos_of_pos (show (b : ℤ) > 0 by linarith)]
      have h7b : a - b ≤ - (b^2 + a * b + 1) := by 
        nlinarith [hk, sq_nonneg (k : ℤ), show k ≤ -1 by omega, sq_nonneg ((b : ℤ) ^ 2 + (a * b : ℤ) + 1 : ℤ)]
      nlinarith [mul_pos (show 0 < a by linarith) (show 0 < b by linarith), sq_nonneg (b : ℤ), sq_nonneg (a - b : ℤ), sq_pos_of_pos (show (a : ℤ) > 0 by linarith), sq_pos_of_pos (show (b : ℤ) > 0 by linarith)]
    · -- k =0 
      have hk1 : k = 0 := by 
        omega 
      rw [hk1] at hk 
      linarith 
  have h8 : (a - b) = 0 := h6 
  linarith