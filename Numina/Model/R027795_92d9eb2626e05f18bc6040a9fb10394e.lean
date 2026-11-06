import Mathlib

theorem algebra_248848 (x y : ℤ) :
    x * y + 3 * y = x ^ 2 + 6 * x + 12 ↔
    (x = -4 ∧ y = -4) ∨ (x = -2 ∧ y = 4) ∨ (x = 0 ∧ y = 4) ∨ (x = -6 ∧ y = -4) := by
  constructor 
  · -- Assume the equation holds, prove the four possible solutions 
    rintro h 
    have eq1 : x ^ 2 + 6 * x + 12 = x * y + 3 * y := by linarith 
    have eq2 : (x + 3) * (x + 3 - y) = -3 := by 
      nlinarith 
    have h1 : (x + 3) * (x + 3 - y) = -3 := eq2 
    have h2 : (x + 3) ∣ -3 := by 
      use (x + 3 - y)
      all_goals linarith 
    have h3 : (x + 3) ∣ (3 : ℤ) := by 
      exact Int.dvd_neg.mp h2 
    have h4 : (x + 3) = 1 ∨ (x + 3) = 3 ∨ (x + 3) = -1 ∨ (x + 3) = -3 := by 
      have h5 : (x + 3) ∣ 3 := h3 
      have h6 : (x + 3) ≤ 3 := by 
        apply Int.le_of_dvd (by norm_num) h5 
      have h7 : (x + 3) ≥ -3 := by 
        have h8 : (- (x + 3)) ∣ 3 := by 
          exact Int.neg_dvd.2 h5 
        have h9 : - (x + 3) ≤ 3 := by 
          apply Int.le_of_dvd (by norm_num) h8 
        omega 
      interval_cases (x + 3) <;> tauto 
    rcases h4 with h5 | h5 | h5 | h5 
    · -- Case (x + 3) = 1 
      have h6 : x + 3 - y = -3 := by 
        rw [h5] at h1 
        linarith 
      have hx : x = -2 := by 
        linarith 
      have hy : y = 4 := by 
        omega 
      right 
      left 
      exact ⟨hx, hy⟩ 
    · -- Case (x + 3) = 3 
      have h6 : x + 3 - y = -1 := by 
        rw [h5] at h1 
        linarith 
      have hx : x = 0 := by 
        linarith 
      have hy : y = 4 := by 
        omega 
      right 
      right 
      left 
      exact ⟨hx, hy⟩ 
    · -- Case (x + 3) = -1 
      have h6 : x + 3 - y = 3 := by 
        rw [h5] at h1 
        linarith 
      have hx : x = -4 := by 
        linarith 
      have hy : y = -4 := by 
        omega 
      left 
      exact ⟨hx, hy⟩ 
    · -- Case (x + 3) = -3 
      have h6 : x + 3 - y = 1 := by 
        rw [h5] at h1 
        linarith 
      have hx : x = -6 := by 
        linarith 
      have hy : y = -4 := by 
        omega 
      right 
      right 
      right 
      exact ⟨hx, hy⟩ 
  · -- Assume one of the solutions, prove the equation 
    rintro (h | h | h | h)
    · -- Case (x = -4 ∧ y = -4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (x = -2 ∧ y = 4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (x = 0 ∧ y = 4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- Case (x = -6 ∧ y = -4)
      rcases h with ⟨rfl, rfl⟩ 
      norm_num