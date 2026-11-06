import Mathlib

theorem algebra_300078 (x y : ℤ) :
    x^3 - x^2 * y + x * y^2 - y^3 = 4 * x^2 - 4 * x * y + 4 * y^2 + 47 ↔
    (x = 7 ∧ y = 4) ∨ (x = -4 ∧ y = -7) ∨ (x = 5 ∧ y = -2) ∨ (x = 2 ∧ y = -5) := by
  constructor
  · -- Assume the equation holds, prove the disjunction of the four pairs
    rintro h
    have h1 : (x ^ 2 + y ^ 2) * (x - y) = 4 * (x ^ 2 - x * y + y ^ 2) + 47 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    have h2 : x - y = 2 ∨ x - y = 3 ∨ x - y = 4 ∨ x - y = 5 ∨ x - y = 6 ∨ x - y = 7 := by
      have h3 : (x - y) ≤ 7 := by
        nlinarith [sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg ((x - y) * (x ^ 2 + y ^ 2) - 4 * (x ^ 2 - x * y + y ^ 2)), sq_nonneg (x + y), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y - 2), sq_nonneg (x - y - 7)]
      have h4 : (x - y) ≥ 2 := by
        nlinarith [sq_nonneg (x ^ 2 + y ^ 2), sq_nonneg ((x - y) * (x ^ 2 + y ^ 2) - 4 * (x ^ 2 - x * y + y ^ 2)), sq_nonneg (x + y), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (x - y - 2), sq_nonneg (x - y - 7)]
      omega
    rcases h2 with (h2 | h2 | h2 | h2 | h2 | h2)
    · -- x - y = 2
      have h3 : x = y + 2 := by
        omega
      rw [show x = y + 2 by linarith] at h1
      nlinarith [sq_nonneg (y)]
    · -- x - y = 3
      have h3 : x = y + 3 := by
        omega
      rw [show x = y + 3 by linarith] at h1
      have h2a : (y - 4) * (y + 7) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h2a) with h3a h4a
      · -- y = 4
        have hy : y = 4 := by linarith
        have hx : x = 7 := by linarith
        simp [hx, hy]
      · -- y = -7
        have hy : y = -7 := by linarith
        have hx : x = -4 := by linarith
        simp [hx, hy]
    · -- x - y = 4
      have h3 : x = y + 4 := by
        omega
      rw [show x = y + 4 by linarith] at h1
      have h2a : (4 : ℤ) * y ^ 2 + 16 * y - 47 = 0 := by
        nlinarith
      have h3a : (4 : ℤ) * y ^ 2 + 16 * y - 47 ≠ 0 := by
        intro h
        have h12 : (4 : ℤ) * y ^ 2 + 16 * y - 47 = 0 := by linarith
        have h7 : (y + 2 : ℤ) ^ 2 * 4 = 63 := by
          nlinarith
        have h9 : ((y + 2 : ℤ) ^ 2) ∣ 63 := by
          use (4)
          all_goals nlinarith
        have h10 : ((y + 2 : ℤ) ^ 2) ≤ 63 := by
          exact Int.le_of_dvd (show (0 : ℤ) < 63 by norm_num) h9
        have h11 : (y + 2 : ℤ) ^ 2 ≥ 0 := by
          apply sq_nonneg
        have h12 : (4 : ℤ) * ((y + 2 : ℤ) ^ 2) = 63 := by
          nlinarith
        omega
      omega
    · -- x - y = 5
      have h3 : x = y + 5 := by
        omega
      rw [show x = y + 5 by linarith] at h1
      have h2a : 3 * y ^ 2 + 15 * y - 11 = 0 := by
        nlinarith
      have h3a : (3 * y ^ 2 + 15 * y - 11 : ℤ) ≠ 0 := by
        intro h
        have h4 : (3 * y ^ 2 + 15 * y - 11 : ℤ) % 3 = 0 := by
          omega
        omega
      omega
    · -- x - y = 6
      have h3 : x = y + 6 := by
        omega
      rw [show x = y + 6 by linarith] at h1
      have h2a : 8 * y ^ 2 + 48 * y + 25 = 0 := by
        nlinarith
      have h3a : (8 * y ^ 2 + 48 * y + 25 : ℤ) ≠ 0 := by
        intro h
        have h5 : (8 * y ^ 2 + 48 * y + 25 : ℤ) % 4 = 0 := by
          omega
        omega
      omega
    · -- x - y = 7
      have h3 : x = y + 7 := by
        omega
      rw [show x = y + 7 by linarith] at h1
      have h2a : (y + 2) * (y + 5) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h2a) with h3a h4a
      · -- y = -2
        have hy : y = -2 := by linarith
        have hx : x = 5 := by linarith
        simp [hx, hy]
      · -- y = -5
        have hy : y = -5 := by linarith
        have hx : x = 2 := by linarith
        simp [hx, hy]
  · -- Assume the disjunction of the four pairs, prove the equation
    rintro (h | h | h | h)
    · -- (7, 4)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (-4, -7)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (5, -2)
      rcases h with ⟨rfl, rfl⟩
      norm_num
    · -- (2, -5)
      rcases h with ⟨rfl, rfl⟩
      norm_num