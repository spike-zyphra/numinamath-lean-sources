import Mathlib

theorem number_theory_607406 (x y : ℤ) : x^2 + 73 = y^2 ↔
    (x = -36 ∧ y = -37) ∨ (x = -36 ∧ y = 37) ∨ (x = 36 ∧ y = -37) ∨ (x = 36 ∧ y = 37) := by
  constructor
  · -- Forward direction: If x^2 + 73 = y^2, prove the disjunction of the four pairs
    intro h
    have h1 : y^2 - x^2 = 73 := by 
      nlinarith
    have h2 : (y - x) * (y + x) = 73 := by
      nlinarith
    have h3 : (y - x) ∣ 73 := by
      use (y + x)
      nlinarith
    have h4 : (y - x) = 1 ∨ (y - x) = 73 ∨ (y - x) = -1 ∨ (y - x) = -73 := by
      have h5 : (y - x) ∣ 73 := h3
      have h6 : (y - x) ≤ 73 := by
        apply Int.le_of_dvd (by norm_num) h5
      have h7 : (y - x) ≥ -73 := by
        have h8 : -(y - x) ∣ 73 := by 
          exact Int.neg_dvd.2 h5
        have h9 : -(y - x) ≤ 73 := by
          apply Int.le_of_dvd (by norm_num) h8
        linarith
      interval_cases h10 : (y - x) <;> tauto
    rcases h4 with (h4 | h4 | h4 | h4)
    · -- Case 1: $y - x = 1$ so $y + x = 73$ 
      have h5 : (y + x) = 73 := by
        rw [h4] at h2
        nlinarith
      have hy : y = 37 := by
        nlinarith
      have hx : x = 36 := by
        nlinarith
      simp [hx, hy]
      <;> tauto
    · -- Case 2: $y - x = 73$ so $y + x = 1$ 
      have h5 : (y + x) = 1 := by
        rw [h4] at h2
        nlinarith
      have hy : y = 37 := by
        nlinarith
      have hx : x = -36 := by
        nlinarith
      simp [hx, hy]
      <;> tauto
    · -- Case 3: $y - x = -1$ so $y + x = -73$ 
      have h5 : (y + x) = -73 := by
        rw [h4] at h2
        nlinarith
      have hy : y = -37 := by
        nlinarith
      have hx : x = -36 := by
        nlinarith
      simp [hx, hy]
      <;> tauto
    · -- Case 4: $y - x = -73$ so $y + x = -1$ 
      have h5 : (y + x) = -1 := by
        rw [h4] at h2
        nlinarith
      have hy : y = -37 := by
        nlinarith
      have hx : x = 36 := by
        nlinarith
      simp [hx, hy]
      <;> tauto
  · -- Backward direction: prove that the pairs satisfy x^2 + 73 = y^2
    rintro (h | h | h | h)
    · -- First pair (-36, -37)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Second pair (-36, 37)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Third pair (36, -37)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- Fourth pair (36, 37)
      rcases h with ⟨rfl, rfl⟩
      norm_num