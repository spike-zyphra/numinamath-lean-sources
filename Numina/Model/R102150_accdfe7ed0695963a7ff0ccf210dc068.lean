import Mathlib

theorem number_theory_294016 (x y : ℤ) :
    x^2 + 73 = y^2 ↔ (x = -36 ∧ y = -37) ∨ (x = -36 ∧ y = 37) ∨
    (x = 36 ∧ y = -37) ∨ (x = 36 ∧ y = 37) := by
  constructor
  · -- Forward direction: if x^2 + 73 = y^2, then (x, y) is one of the four pairs
    intro h
    have h1 : y^2 - x^2 = 73 := by linarith
    have h2 : (y - x) * (y + x) = 73 := by
      linarith [h1]
    have h3 : (y - x) = 1 ∨ (y - x) = 73 ∨ (y - x) = -1 ∨ (y - x) = -73 := by
      have h4 : (y - x) ∣ 73 := by
        use (y + x)
        linarith [h2]
      have h5 : (y - x) = 1 ∨ (y - x) = 73 ∨ (y - x) = -1 ∨ (y - x) = -73 := by
        have h6 : (y - x) ∣ 73 := h4
        have h7 : (y - x) ≤ 73 := by
          apply Int.le_of_dvd (by norm_num) h6
        have h8 : (y - x) ≥ -73 := by
          have h9 : -(y - x) ∣ 73 := by
            exact Int.neg_dvd.mpr h6
          have h10 : -(y - x) ≤ 73 := by
            apply Int.le_of_dvd (by norm_num) h9
          linarith
        interval_cases (y - x) <;> omega
      exact h5
    rcases h3 with h4 | h4 | h4 | h4
    · -- Case y - x = 1, solve
      have h5 : y + x = 73 := by
        rw [h4] at h2
        linarith [h2]
      have h6 : y = 37 := by
        linarith [h4, h5]
      have h7 : x = 36 := by
        linarith [h5, h6]
      exact Or.inr (Or.inr (Or.inr ⟨h7, h6⟩))
    · -- Case y - x = 73, solve
      have h5 : y + x = 1 := by
        rw [h4] at h2
        linarith [h2]
      have h6 : y = 37 := by
        linarith [h4, h5]
      have h7 : x = -36 := by
        linarith [h5, h6]
      exact Or.inr (Or.inl ⟨h7, h6⟩)
    · -- Case y - x = -1, solve
      have h5 : y + x = -73 := by
        rw [h4] at h2
        linarith [h2]
      have h6 : y = -37 := by
        linarith [h4, h5]
      have h7 : x = -36 := by
        linarith [h5, h6]
      exact Or.inl ⟨h7, h6⟩
    · -- Case y - x = -73, solve leads to x = 36 and y = -37
      have h5 : y + x = -1 := by
        rw [h4] at h2
        linarith [h2]
      have h6 : y = -37 := by
        linarith [h4, h5]
      have h7 : x = 36 := by
        linarith [h5, h6]
      exact Or.inr (Or.inr (Or.inl ⟨h7, h6⟩))
  · -- Backward direction: each pair satisfies x^2 + 73 = y^2
    rintro (h | h | h | h)
    · -- Case (x = -36 ∧ y = -37)
      rw [h.1, h.2]
      norm_num
    · -- Case (x = -36 ∧ y = 37)
      rw [h.1, h.2]
      norm_num
    · -- Case (x = 36 ∧ y = -37)
      rw [h.1, h.2]
      norm_num
    · -- Case (x = 36 ∧ y = 37)
      rw [h.1, h.2]
      norm_num