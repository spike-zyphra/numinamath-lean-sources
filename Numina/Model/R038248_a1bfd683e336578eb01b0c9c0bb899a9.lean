import Mathlib

theorem algebra_280492 {x y : ℤ} (h : x^2 - x * y - 6 * y^2 + 2 * x + 19 * y = 18) :
    (x - 3 * y + 5) * (x + 2 * y - 3) = 3 ↔ (x = 2 ∧ y = 2) ∨ (x = -2 ∧ y = 2) := by
  constructor
  · -- Assume (x - 3 * y + 5) * (x + 2 * y - 3) = 3, prove (x = 2 ∧ y = 2) ∨ (x = -2 ∧ y = 2)
    intro h1
    have h2 : (x - 3 * y + 5) * (x + 2 * y - 3) = 3 := h1
    have h3 : (x - 3 * y + 5) ∣ 3 := by 
      use (x + 2 * y - 3)
      all_goals nlinarith
    have h4 : (x - 3 * y + 5) = 1 ∨ (x - 3 * y + 5) = 3 ∨ (x - 3 * y + 5) = -1 ∨ (x - 3 * y + 5) = -3 := by
      have h5 : (x - 3 * y + 5) ∣ 3 := h3
      have h6 : (x - 3 * y + 5) ≤ 3 := by 
        apply Int.le_of_dvd (by norm_num) h5
      have h7 : (x - 3 * y + 5) ≥ -3 := by 
        have h8 : (- (x - 3 * y + 5)) ∣ 3 := by 
          exact Int.neg_dvd.2 h5
        have h9 : - (x - 3 * y + 5) ≤ 3 := by 
          apply Int.le_of_dvd (by norm_num) h8
        omega
      interval_cases (x - 3 * y + 5) <;> tauto
    rcases h4 with (h11 | h11 | h11 | h11)
    · -- Case where x - 3 * y + 5 = 1
      have h12 : (x + 2 * y - 3) = 3 := by 
        rw [h11] at h2
        linarith
      have eq1 : x = 2 := by
        omega
      have eq2 : y = 2 := by 
        omega
      left
      exact ⟨eq1, eq2⟩
    · -- Case where x - 3 * y + 5 = 3
      have h12 : (x + 2 * y - 3) = 1 := by 
        rw [h11] at h2
        linarith
      exfalso
      omega
    · -- Case where x - 3 * y + 5 = -1
      have h12 : (x + 2 * y - 3) = -3 := by
        rw [h11] at h2
        linarith
      exfalso
      omega
    · -- Case where x - 3 * y + 5 = -3
      have h12 : (x + 2 * y - 3) = -1 := by
        rw [h11] at h2
        linarith
      have eq1 : x = -2 := by
        omega
      have eq2 : y = 2 := by 
        omega
      right
      exact ⟨eq1, eq2⟩
  · -- Assume (x = 2 ∧ y = 2) ∨ (x = -2 ∧ y = 2), prove (x - 3 * y + 5) * (x + 2 * y - 3) = 3
    rintro (h1 | h2)
    · -- Case where (x = 2 ∧ y = 2)
      rcases h1 with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case where (x = -2 ∧ y = 2)
      rcases h2 with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num