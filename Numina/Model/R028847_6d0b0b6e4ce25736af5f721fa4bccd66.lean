import Mathlib

theorem number_theory_304784 (n : ℕ) (d : ℕ) (h₀ : d ≠ 1) (h₁ : 19 * n + 14 ≡ 0 [ZMOD d]) (h₂ : 10 * n + 3 ≡ 0 [ZMOD d]) :
    d = 83 := by
  simp [Int.ModEq] at h₁ h₂
  have h3 : (d : ℤ) ∣ (19 * (n : ℤ) + 14) := by 
    simpa using h₁ 
  have h4 : (d : ℤ) ∣ (10 * (n : ℤ) + 3) := by 
    simpa using h₂ 
  have h5 : (d : ℤ) ∣ (83 : ℤ) := by 
    have h7 : (d : ℤ) ∣ (19 * (10 * (n : ℤ) + 3) - 10 * (19 * (n : ℤ) + 14)) := by 
      have h8 : (d : ℤ) ∣ (19 * (10 * (n : ℤ) + 3)) := by 
        apply dvd_mul_of_dvd_right 
        exact h4 
      have h9 : (d : ℤ) ∣ (10 * (19 * (n : ℤ) + 14)) := by 
        apply dvd_mul_of_dvd_right 
        exact h3 
      apply Int.dvd_sub 
      · exact h8 
      · exact h9 
    have h6 : (19 * (10 * (n : ℤ) + 3) - 10 * (19 * (n : ℤ) + 14)) = (-83 : ℤ) := by 
      ring 
    rw [h6] at h7 
    have h8 : (d : ℤ) ∣ 83 := by 
      exact Int.dvd_neg.mp h7 
    exact h8 
  have h7 : (d : ℕ) ∣ 83 := by 
    exact Int.ofNat_dvd_right.mp h5 
  have h8 : d ∣ 83 := by 
    exact h7 
  have h9 : d = 83 := by 
    have h10 : d ∣ 83 := h8 
    have h11 : d ≤ 83 := by 
      exact Nat.le_of_dvd (by norm_num) h10 
    have h12 : d ≠ 1 := h₀ 
    interval_cases d <;> norm_num at h10 h12 ⊢ <;> tauto 
  exact h9