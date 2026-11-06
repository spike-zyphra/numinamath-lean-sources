import Mathlib

theorem algebra_256597 (x y : ℤ) :
    x^2 + x * y - y = 2 ↔ (x = 2 ∧ y = -2) ∨ (x = 0 ∧ y = -2) := by
  constructor
  · -- Assume x^2 + x * y - y = 2, prove (x = 2 ∧ y = -2) ∨ (x = 0 ∧ y = -2)
    intro h
    have h1 : x ^ 2 + y * (x - 1) = 2 := by
      linarith
    have h2 : (x - 1) ∣ 1 := by
      have h3 : (x - 1) * (y + x + 1) = 1 := by
        nlinarith
      use (y + x + 1)
      all_goals linarith
    have h4 : (x - 1) = 1 ∨ (x - 1) = -1 := by
      have h5 : (x - 1) ∣ 1 := h2
      have h6 : (x - 1) ≤ 1 := by
        exact Int.le_of_dvd (by norm_num) h5
      have h7 : (x - 1) ≥ -1 := by
        have h8 : (- (x - 1)) ∣ 1 := by
          exact Int.neg_dvd.2 h5
        have h9 : - (x - 1) ≤ 1 := by
          exact Int.le_of_dvd (by norm_num) h8
        omega
      interval_cases (x - 1) <;> tauto
    rcases h4 with h5 | h6
    · -- x - 1 = 1 => x = 2
      have hx : x = 2 := by
        linarith
      have hy : y = -2 := by
        rw [hx] at h
        nlinarith
      left
      exact ⟨hx, hy⟩
    · -- x - 1 = -1 => x = 0
      have hx : x = 0 := by
        linarith
      have hy : y = -2 := by
        rw [hx] at h
        nlinarith
      right
      exact ⟨hx, hy⟩
  · -- Show that (x = 2 ∧ y = -2) ∨ (x = 0 ∧ y = -2) implies x^2 + x * y - y = 2
    rintro (h | h)
    · -- x = 2 ∧ y = -2
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- x = 0 ∧ y = -2
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num