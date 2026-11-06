import Mathlib

theorem algebra_101622 (x y : ℤ) : 2*x^3+x*y-7=0 ↔
    (x=-7 ∧ y=-99) ∨ (x=-1 ∧ y=-9) ∨ (x=1 ∧ y=5) ∨ (x=7 ∧ y=-97) := by
  constructor
  · -- Assume 2 x^3 + x y - 7 = 0, prove the disjunction of the four pairs
    rintro h
    have h1 : x ∣ 7 := by
      use 2 * x^2 + y
      nlinarith
    have h2 : x = 1 ∨ x = -1 ∨ x = 7 ∨ x = -7 := by
      have h3 : x ∣ 7 := h1
      have h4 : x ∣ 7 := h3
      have h5 : x ≤ 7 := by
        apply Int.le_of_dvd (by norm_num) h4
      have h6 : x ≥ -7 := by
        have h7 : (-x) ∣ 7 := by
          exact Int.neg_dvd.2 h4
        have h8 : -x ≤ 7 := by
          apply Int.le_of_dvd (by norm_num) h7
        omega
      interval_cases x <;> tauto
    rcases h2 with (h2 | h2 | h2 | h2)
    · -- Assume x = 1, prove y = 5
      have h3 : y = 5 := by
        rw [show x = 1 by linarith] at h
        linarith
      simp [h2, h3]
    · -- Assume x = -1, prove y = -9
      have h3 : y = -9 := by
        rw [show x = -1 by linarith] at h
        linarith
      simp [h2, h3]
    · -- Assume x = 7, prove y = -97
      have h3 : y = -97 := by
        rw [show x = 7 by linarith] at h
        linarith
      simp [h2, h3]
    · -- Assume x = -7, prove y = -99
      have h3 : y = -99 := by
        rw [show x = -7 by linarith] at h
        linarith
      simp [h2, h3]
  · -- Show that the four pairs satisfy 2x^3 + x y -7 = 0
    rintro (h | h | h | h)
    · -- Check (-7, -99)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Check (-1, -9)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Check (1, 5)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Check (7, -97)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num