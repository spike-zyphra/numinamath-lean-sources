import Mathlib

theorem algebra_4744 (x : ℝ) (hx : x^2 + 3 * x ≠ 0 ∧ x^2 + 9 * x + 18 ≠ 0 ∧ x^2 + 15 * x + 54 ≠ 0) :
    1 / (x^2 + 3 * x) + 1 / (x^2 + 9 * x + 18) + 1 / (x^2 + 15 * x + 54) = 3 / (2 * x + 18) ↔ x = 2 := by
  constructor
  · -- Forward direction: suppose the equation holds, prove x = 2
    intro h_eq
    have h1 : x ^ 2 + 3 * x ≠ 0 := hx.1
    have h2 : x ^ 2 + 9 * x + 18 ≠ 0 := hx.2.1
    have h3 : x ^ 2 + 15 * x + 54 ≠ 0 := hx.2.2
    have h4 : 2 * x + 18 ≠ 0 := by
      intro h
      have h5 : x = -9 := by linarith
      rw [h5] at h3
      norm_num at h3
      all_goals norm_num at h3
    field_simp [h1, h2, h3, h4] at h_eq
    ring_nf at h_eq
    have h5 : (x - 2) * (x + 3) * (x + 6) * (x + 9) = 0 := by
      nlinarith [sq_nonneg (x + 3), sq_nonneg (x + 6), sq_nonneg (x + 9), sq_nonneg (x - 2), sq_nonneg (x), sq_nonneg (x - 3), sq_nonneg (x + 4.5)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    cases' (mul_eq_zero.mp h6) with h8 h9
    cases' (mul_eq_zero.mp h8) with h10 h11
    · -- x - 2 = 0, so x = 2
      linarith
    · -- x + 3 = 0, so x = -3. Show contradiction with h1
      have h12 : x = -3 := by linarith
      rw [h12] at h1
      norm_num at h1
    · -- x + 6 = 0, so x = -6. Show contradiction with h2
      have h13 : x = -6 := by linarith
      rw [h13] at h2
      norm_num at h2
    · -- x + 9 = 0, so x = -9. Show contradiction with h3
      have h14 : x = -9 := by linarith
      rw [h14] at h3
      norm_num at h3
  · -- Backward direction: suppose x = 2, prove the equation holds
    intro h_eq
    rw [h_eq]
    norm_num