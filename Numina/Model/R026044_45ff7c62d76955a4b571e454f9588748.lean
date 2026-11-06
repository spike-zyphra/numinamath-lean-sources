import Mathlib

theorem algebra_114733 (x y : ℤ) :
    x^2 = y^2 + 2 * y + 13 ↔ (x = 4 ∧ y = -3) ∨ (x = 4 ∧ y = 1) ∨ (x = -4 ∧ y = 1) ∨ (x = -4 ∧ y = -3) := by
  constructor
  · -- First, prove the forward direction: if $(x, y)$ satisfies the equation, then it is one of the four solutions.
    intro h
    have h1 : x^2 = y^2 + 2 * y + 13 := h
    have h2 : x^2 - (y + 1)^2 = 12 := by
      nlinarith
    have h3 : (x - y - 1) * (x + y + 1) = 12 := by
      ring_nf at h2 ⊢
      linarith
    have h4 : x - y - 1 ∣ 12 := by
      use x + y + 1
      all_goals linarith
    have h5 : x - y - 1 ≤ 12 := by
      apply Int.le_of_dvd (by norm_num) h4
    have h6 : x - y - 1 ≥ -12 := by
      have h7 : - (x - y - 1) ∣ 12 := by
        exact Int.neg_dvd.2 h4
      have h8 : - (x - y - 1) ≤ 12 := by
        apply Int.le_of_dvd (by norm_num) h7
      omega
    interval_cases k : x - y - 1 <;> omega
  · -- Now the reverse direction: each of the four pairs satisfies the equation.
    rintro (h | h | h | h)
    · -- First pair: (4, -3)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Second pair: (4, 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Third pair: (-4, 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Fourth pair: (-4, -3)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num