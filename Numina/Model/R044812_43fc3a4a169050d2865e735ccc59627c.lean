import Mathlib

theorem number_theory_5225 (x y : ℤ) : x^3 - y^3 = 91 ↔
    (x = 3 ∧ y = -4) ∨ (x = 4 ∧ y = -3) ∨ (x = 6 ∧ y = 5) ∨ (x = -5 ∧ y = -6) := by
  constructor
  · -- First direction: given x^3 - y^3 = 91, prove the four possible pairs.
    intro h
    have h1 : x^3 - y^3 = 91 := h
    have h2 : (x - y) * (x^2 + x * y + y^2) = 91 := by
      nlinarith
    have h3 : (x - y) ∣ 91 := by
      use (x^2 + x * y + y^2)
      all_goals linarith
    have h4 : (x - y) = 1 ∨ (x - y) = 7 ∨ (x - y) = 13 ∨ (x - y) = 91 ∨ (x - y) = -1 ∨ (x - y) = -7 ∨ (x - y) = -13 ∨ (x - y) = -91 := by
      have h3' : (x - y) ∣ 91 := h3
      have h5 : (x - y) ≤ 91 := by
        apply Int.le_of_dvd (by norm_num) h3'
      have h6 : (x - y) ≥ -91 := by
        have h7 : -(x - y) ∣ 91 := by
          exact Int.neg_dvd.2 h3'
        have h8 : -(x - y) ≤ 91 := by
          apply Int.le_of_dvd (by norm_num) h7
        linarith
      interval_cases h7 : (x - y) <;> tauto
    rcases h4 with (h4 | h4 | h4 | h4 | h4 | h4 | h4 | h4)
    · -- case (x - y) = 1
      have h5 : x^2 + x * y + y^2 = 91 := by
        rw [show (x - y) = 1 by linarith] at h2
        linarith
      have h6 : x = y + 1 := by
        linarith
      rw [h6] at h5
      have h7 : (y - 5) * (y + 6) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h7) with h8 h9
      · -- case y = 5
        have hy : y = 5 := by linarith
        have hx : x = 6 := by linarith [h6, hy]
        simp [hx, hy]
      · -- case y = -6
        have hy : y = -6 := by linarith
        have hx : x = -5 := by linarith [h6, hy]
        simp [hx, hy]
    · -- case (x - y) = 7
      have h5 : x^2 + x * y + y^2 = 13 := by
        rw [show (x - y) = 7 by linarith] at h2
        linarith
      have h6 : x = y + 7 := by
        linarith
      rw [h6] at h5
      have h7 : (y + 3) * (y + 4) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h7) with h8 h9
      · -- case y = -3
        have hy : y = -3 := by linarith
        have hx : x = 4 := by linarith [h6, hy]
        simp [hx, hy]
      · -- case y = -4
        have hy : y = -4 := by linarith
        have hx : x = 3 := by linarith [h6, hy]
        simp [hx, hy]
    · -- case (x - y) = 13
      have h5 : x^2 + x * y + y^2 = 7 := by
        rw [show (x - y) = 13 by linarith] at h2
        linarith
      have h6 : x = y + 13 := by
        linarith
      rw [h6] at h5
      nlinarith [sq_nonneg (y * 3 + 13 : ℤ), sq_nonneg (y + 4 : ℤ), sq_nonneg (y + 10 : ℤ)]
    · -- case (x - y) = 91
      have h5 : x^2 + x * y + y^2 = 1 := by
        rw [show (x - y) = 91 by linarith] at h2
        linarith
      have h6 : x = y + 91 := by
        linarith
      rw [h6] at h5
      nlinarith [sq_nonneg (y + 45 : ℤ), sq_nonneg ((y + 45 : ℤ) * 3 + 1)]
    · -- case (x - y) = -1
      have h5 : x^2 + x * y + y^2 = -91 := by
        rw [show (x - y) = -1 by linarith] at h2
        linarith
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    · -- case (x - y) = -7
      have h5 : x^2 + x * y + y^2 = -13 := by
        rw [show (x - y) = -7 by linarith] at h2
        linarith
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    · -- case (x - y) = -13
      have h5 : x^2 + x * y + y^2 = -7 := by
        rw [show (x - y) = -13 by linarith] at h2
        linarith
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
    · -- case (x - y) = -91
      have h5 : x^2 + x * y + y^2 = -1 := by
        rw [show (x - y) = -91 by linarith] at h2
        linarith
      nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (x + y : ℤ), sq_nonneg (x : ℤ), sq_nonneg (y : ℤ)]
  · -- Second direction: given the four possible pairs, prove x^3 - y^3 = 91.
    rintro (h | h | h | h)
    · -- First pair (3, -4)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Second pair (4, -3)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Third pair (6, 5)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Fourth pair (-5, -6)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num