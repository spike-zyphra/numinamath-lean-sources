import Mathlib

theorem algebra_233971 (x y : ℤ) : x^2 - x * y - 2 * y^2 = 7 ↔
    (x = 3 ∧ y = -2) ∨ (x = 5 ∧ y = 2) ∨ (x = -3 ∧ y = 2) ∨ (x = -5 ∧ y = -2) := by
  constructor
  · -- Forward direction: if the equation holds, then (x, y) is one of the four given pairs.
    intro h 
    have h1 : (x - 2 * y) * (x + y) = 7 := by
      nlinarith 
    -- Now, we need to find all integer solutions to (x - 2*y)*(x + y) = 7.
    -- Since 7 is a prime, the factors must be in the pairs: (1, 7), (7, 1), (-1, -7), (-7, -1).
    have h2 : (x - 2 * y) * (x + y) = 7 := h1 
    have h3 : (x - 2 * y) ∣ 7 := by 
      use (x + y)
      all_goals nlinarith 
    have h4 : (x - 2 * y) = 1 ∨ (x - 2 * y) = 7 ∨ (x - 2 * y) = -1 ∨ (x - 2 * y) = -7 := by 
      have h3' : (x - 2 * y) ∣ 7 := h3 
      have h5 : (x - 2 * y) ≤ 7 := by 
        apply Int.le_of_dvd (by norm_num) h3' 
      have h6 : (x - 2 * y) ≥ -7 := by
        have h7 : - (x - 2 * y) ∣ 7 := by
          exact Int.neg_dvd.2 h3' 
        have h8 : - (x - 2 * y) ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num) h7 
        omega 
      interval_cases (x - 2 * y) <;> try { tauto } 
    rcases h4 with h5 | h6 | h7 | h8 
    · -- Case where (x - 2*y) = 1, so (x + y) = 7
      have h5' : x + y = 7 := by 
        rw [h5] at h1 
        have : (x + y : ℤ) = 7 := by
          nlinarith 
        linarith 
      have hy1 : y = 2 := by 
        omega 
      have hx1 : x = 5 := by
        linarith [h5, hy1] 
      simp [hx1, hy1]
    · -- Case (x - 2*y) = 7, so (x + y) = 1
      have h6' : x + y = 1 := by
        rw [h6] at h1 
        have : (x + y : ℤ) = 1 := by
          nlinarith 
        linarith 
      have hy2 : y = -2 := by 
        omega 
      have hx2 : x = 3 := by
        linarith [h6, hy2] 
      simp [hx2, hy2]
    · -- Case (x - 2*y) = -1, so (x + y) = -7
      have h7' : x + y = -7 := by
        rw [h7] at h1 
        have : (x + y : ℤ) = -7 := by
          nlinarith 
        linarith 
      have hy3 : y = -2 := by 
        omega 
      have hx3 : x = -5 := by
        linarith [h7, hy3] 
      simp [hx3, hy3]
    · -- Case (x - 2*y) = -7, so (x + y) = -1
      have h8' : x + y = -1 := by
        rw [h8] at h1 
        have : (x + y : ℤ) = -1 := by
          nlinarith 
        linarith 
      have hy4 : y = 2 := by 
        omega 
      have hx4 : x = -3 := by
        linarith [h8, hy4] 
      simp [hx4, hy4]
  · -- Backward direction: each of the four pairs satisfies the equation.
    rintro (h | h | h | h)
    · -- Check the first pair (3, -2)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Check the second pair (5, 2)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Check the third pair (-3, 2)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Check the fourth pair (-5, -2)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num