import Mathlib

theorem number_theory_55989 (a b : ℤ) (_ : 0 < a) (h₀ : 0 < b)
    (h₁ : (a^3 - a^2 + 1) * (b^3 - b^2 + 2) = 2020) :
    10 * a + b = 53 := by

  have h2 : a ≤ 11 := by
    by_contra h3
    push_neg at h3
    have h3' : a^3 - a^2 + 1 ≥ 1585 := by
      nlinarith [sq_nonneg (a - 12), sq_nonneg (a - 11), sq_pos_of_pos (show (0 : ℤ) < a by linarith), sq_nonneg (a^2 - 144), sq_nonneg (a - 12)]
    have h4 : b^3 - b^2 + 2 ≥ 2 := by
      nlinarith [sq_nonneg (b - 1), sq_nonneg (b^2 - 1), sq_pos_of_pos (show (0 : ℤ) < b by linarith), sq_nonneg (b - 2)]
    have h5 : (a^3 - a^2 + 1) * (b^3 - b^2 + 2) > (2020 : ℤ) := by
      nlinarith [h3', h4, mul_pos (show (0 : ℤ) < a by linarith) (show (0 : ℤ) < b by linarith)]
    nlinarith
  have h3 : b ≤ 12 := by
    by_contra h4
    push_neg at h4
    have h4' : b^3 - b^2 + 2 ≥ 2030 := by
      nlinarith [sq_nonneg (b - 13), sq_nonneg (b - 12), sq_pos_of_pos (show (0 : ℤ) < b by linarith), sq_nonneg (b^2 - 169), sq_nonneg (b - 13)]
    have h5 : a^3 - a^2 + 1 ≥ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (a^2 - 1), sq_pos_of_pos (show (0 : ℤ) < a by linarith)]
    have h6 : (a^3 - a^2 + 1) * (b^3 - b^2 + 2) > (2020 : ℤ) := by
      nlinarith [h4', h5, mul_pos (show (0 : ℤ) < a by linarith) (show (0 : ℤ) < b by linarith)]
    nlinarith
  interval_cases a <;> interval_cases b <;> omega