import Mathlib

theorem algebra_187108 (x y : ℤ) :
    x * y + 3 * x - 2 * y - 3 = 0 ↔
    (x = -1 ∧ y = -2) ∨ (x = 1 ∧ y = 0) ∨ (x = 3 ∧ y = -6) ∨ (x = 5 ∧ y = -4) := by 
  constructor
  · -- Forward direction
    intro h
    have h1 : (x - 2) * (y + 3) = -3 := by
      nlinarith
    have h2 : (x - 2) ∣ -3 := by 
      use y + 3
      all_goals linarith
    have h3 : (x - 2) ∣ 3 := by 
      have h4 : (x - 2) ∣ -3 := h2
      have h5 : (x - 2) ∣ 3 := by
        exact Int.dvd_neg.mp h4
      exact h5
    have h6 : (x - 2) = 1 ∨ (x - 2) = -1 ∨ (x - 2) = 3 ∨ (x - 2) = -3 := by 
      have h7 : (x - 2) ∣ 3 := h3
      have h8 : (x - 2) ≤ 3 := by 
        exact Int.le_of_dvd (by norm_num) h7
      have h9 : (x - 2) ≥ -3 := by 
        have h9 : -(x - 2) ∣ 3 := by 
          exact Int.neg_dvd.2 h7
        have h10 : -(x - 2) ≤ 3 := by 
          exact Int.le_of_dvd (by norm_num) h9
        omega
      interval_cases (x - 2) <;> try { tauto }
    rcases h6 with (h6 | h6 | h6 | h6)
    · -- Case where x - 2 = 1, so x = 3 and y + 3 = -3, so y = -6
      have hx : x = 3 := by linarith
      have hy : y = -6 := by
        nlinarith
      simp [hx, hy]
    · -- Case where x - 2 = -1, so x = 1 and y + 3 = 3, so y = 0
      have hx : x = 1 := by linarith
      have hy : y = 0 := by
        nlinarith
      simp [hx, hy]
    · -- Case where x - 2 = 3, so x = 5 and y + 3 = -1, so y = -4
      have hx : x = 5 := by linarith
      have hy : y = -4 := by
        nlinarith
      simp [hx, hy]
    · -- Case where x - 2 = -3, so x = -1 and y + 3 = 1, so y = -2
      have hx : x = -1 := by linarith
      have hy : y = -2 := by
        nlinarith
      simp [hx, hy]
  · -- Backward direction
    rintro (h | h | h | h)
    · -- Case where (x = -1 ∧ y = -2)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case where (x = 1 ∧ y = 0)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case where (x = 3 ∧ y = -6)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case where (x = 5 ∧ y = -4)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num