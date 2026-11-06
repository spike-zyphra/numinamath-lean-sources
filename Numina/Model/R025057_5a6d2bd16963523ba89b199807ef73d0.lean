import Mathlib

theorem inequalities_248575 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1 / a + 1 / c = 2 / b) (h1 : a * c > 0) :
    (a + b) / (2 * a - b) + (c + b) / (2 * c - b) ≥ 4 := by

  have eq1 : b * (a + c) = 2 * a * c := by
    field_simp [ha, hc, hb] at h ⊢
    linarith

  have h2a : 2 * a - b ≠ 0 := by
    by_contra h_eq
    have h2a : b = 2 * a := by linarith
    rw [h2a] at eq1
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < a * c by nlinarith [h1]), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hc]

  have h2b : 2 * c - b ≠ 0 := by
    by_contra h_eq
    have h2b : b = 2 * c := by linarith
    rw [h2b] at eq1
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < a * c by nlinarith [h1]), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hc]

  have h3 : (a + b) / (2 * a - b) + (c + b) / (2 * c - b) - 4 ≥ 0 := by
    have h4 : (a + b) / (2 * a - b) + (c + b) / (2 * c - b) - 4 =
        ( (a + b) * (2 * c - b) + (c + b) * (2 * a - b) - 4 * (2 * a - b) * (2 * c - b) ) / ( (2 * a - b) * (2 * c - b) ) := by
      field_simp [h2a, h2b]
      <;> ring
    rw [h4]
    have h5 : (a + b) * (2 * c - b) + (c + b) * (2 * a - b) - 4 * (2 * a - b) * (2 * c - b) ≥ 0 := by
      nlinarith [sq_nonneg (a - c), sq_nonneg (b - (a + c)), sq_nonneg (a + c - b), sq_nonneg (a * b - c * b), sq_nonneg (a * c - b^2), sq_nonneg (a - c), sq_nonneg (a + c - 2 * b), sq_nonneg (2 * a - 2 * c - b), sq_nonneg (2 * a - b), sq_nonneg (2 * c - b), sq_nonneg (a * c), sq_pos_of_pos h1, sq_nonneg (b ^ 2 - 4 * a * c), sq_nonneg (a * b), sq_nonneg (c * b)]
    have h6 : (2 * a - b) * (2 * c - b) > 0 := by
      nlinarith [sq_pos_of_pos h1, sq_nonneg (a + c), sq_nonneg (b ^ 2 - a * c), sq_nonneg (b ^ 2 - 4 * a * c), sq_nonneg (a * b), sq_nonneg (c * b) ]
    apply div_nonneg
    · linarith
    · nlinarith

  linarith