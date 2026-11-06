import Mathlib
theorem algebra_604955 (x y : ℤ) (hx : x > 0) (hy : y > 0) : x * (x - y) = 8 * y - 7 ↔ (x, y) = (63, 56) := by 
  constructor
  · -- Assume x * (x - y) = 8 * y - 7, prove (x, y) = (63, 56)
    intro h
    have eq1 : x ^ 2 + 7 = y * (x + 8) := by 
      nlinarith [h]
    have h2 : (x + 8) ∣ 71 := by
      use y - x + 8
      nlinarith [eq1]
    have h3 : (x + 8) = 1 ∨ (x + 8) = 71 ∨ (x + 8) = -1 ∨ (x + 8) = -71 := by 
      have h4 : (x + 8) ∣ 71 := h2
      have h5 : (x + 8) ≤ 71 := by 
        apply Int.le_of_dvd (by norm_num) h4 
      have h6 : (x + 8) ≥ -71 := by 
        have h7 : -(x + 8) ∣ 71 := by 
          exact Int.neg_dvd.2 h4 
        have h8 : -(x + 8) ≤ 71 := by 
          apply Int.le_of_dvd (by norm_num) h7 
        omega 
      interval_cases h7 : (x + 8) <;> tauto 
    rcases h3 with (h4 | h4 | h4 | h4)
    · -- Case x + 8 = 1, so x = -7 which contradicts x > 0 
      have h5 : x = -7 := by linarith
      linarith
    · -- Case x + 8 = 71, so x = 63 
      have hx2 : x = 63 := by linarith
      have hy2 : y = 56 := by 
        rw [hx2] at eq1 
        nlinarith 
      simp [hx2, hy2]
    · -- Case x + 8 = -1, so x = -9 which contradicts x > 0 
      have h5 : x = -9 := by linarith
      linarith
    · -- Case x + 8 = -71, so x = -79 which contradicts x > 0 
      have h5 : x = -79 := by linarith 
      linarith
  · -- Assume (x, y) = (63, 56), prove x * (x - y) = 8 * y - 7 
    rintro ⟨rfl, rfl⟩ 
    norm_num