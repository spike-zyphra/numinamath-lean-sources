import Mathlib

theorem algebra_116978 (x y : ℤ) (hx : 0 < x) (hy : 0 < y) :
    x^2 = y^2 + 7 * y + 6 ↔ (x, y) = (6, 3) := by
  constructor
  · -- First direction: x² = y² + 7y + 6 → (x, y) = (6, 3)
    intro h 
    have h1 : 4 * x ^ 2 = (2 * y + 7) ^ 2 - 25 := by
      nlinarith
    have h2 : (2 * y + 7 - 2 * x) * (2 * y + 7 + 2 * x) = 25 := by 
      nlinarith
    have h3 : (2 * y + 7 - 2 * x) ∣ 25 := by 
      use (2 * y + 7 + 2 * x)
      all_goals linarith
    have h4 : (2 * y + 7 - 2 * x) = 1 ∨ (2 * y + 7 - 2 * x) = 5 ∨ (2 * y + 7 - 2 * x) = 25 ∨ 
        (2 * y + 7 - 2 * x) = -1 ∨ (2 * y + 7 - 2 * x) = -5 ∨ (2 * y + 7 - 2 * x) = -25 := by
      have h6 : (2 * y + 7 - 2 * x) ∣ 25 := h3
      have h7 : (2 * y + 7 - 2 * x) ≤ 25 := by 
        apply Int.le_of_dvd (by norm_num) h6
      have h8 : (2 * y + 7 - 2 * x) ≥ -25 := by 
        have h9 : -(2 * y + 7 - 2 * x) ∣ 25 := by 
          exact Int.neg_dvd.2 h6
        have h10 : -(2 * y + 7 - 2 * x) ≤ 25 := by 
          apply Int.le_of_dvd (by norm_num) h9
        omega
      interval_cases h1 : (2 * y + 7 - 2 * x) <;> tauto
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4)
    · -- Case where (2 * y + 7 - 2 * x) = 1, so (2 * y + 7 + 2 * x) = 25
      have h5 : (2 * y + 7 + 2 * x) = 25 := by
        rw [show (2 * y + 7 - 2 * x) = 1 by linarith] at h2 
        nlinarith
      have h6 : y = 3 := by
        omega 
      have h7 : x = 6 := by
        omega
      simp [h7, h6]
    · -- Case where (2 * y + 7 - 2 * x) = 5, so (2 * y + 7 + 2 * x) = 5
      have h5 : (2 * y + 7 + 2 * x) = 5 := by 
        rw [show (2 * y + 7 - 2 * x) = 5 by linarith] at h2 
        nlinarith
      exfalso
      linarith
    · -- Case where (2 * y + 7 - 2 * x) = 25, so (2 * y + 7 + 2 * x) = 1
      have h5 : (2 * y + 7 + 2 * x) = 1 := by 
        rw [show (2 * y + 7 - 2 * x) = 25 by linarith] at h2 
        nlinarith
      exfalso
      linarith
    · -- Case where (2 * y + 7 - 2 * x) = -1, so (2 * y + 7 + 2 * x) = -25
      have h5 : (2 * y + 7 + 2 * x) = -25 := by 
        rw [show (2 * y + 7 - 2 * x) = -1 by linarith] at h2 
        nlinarith
      exfalso
      linarith
    · -- Case where (2 * y + 7 - 2 * x) = -5, so (2 * y + 7 + 2 * x) = -5
      have h5 : (2 * y + 7 + 2 * x) = -5 := by 
        rw [show (2 * y + 7 - 2 * x) = -5 by linarith] at h2 
        nlinarith
      exfalso
      linarith
    · -- Case where (2 * y + 7 - 2 * x) = -25, so (2 * y + 7 + 2 * x) = -1
      have h5 : (2 * y + 7 + 2 * x) = -1 := by 
        rw [show (2 * y + 7 - 2 * x) = -25 by linarith] at h2 
        nlinarith
      exfalso 
      linarith
  · -- Backward implication: (x, y) = (6, 3) → x² = y² + 7y + 6 
    rintro ⟨rfl, rfl⟩ 
    norm_num