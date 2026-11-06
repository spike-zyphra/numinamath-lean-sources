import Mathlib

theorem algebra_291651 {x y z : ℝ}
    (h1 : x^2 - y * z = -23)
    (h2 : y^2 - z * x = -4)
    (h3 : z^2 - x * y = 34) :
    (x = 5 ∧ y = 6 ∧ z = 8) ∨ (x = -5 ∧ y = -6 ∧ z = -8) := by
  have h4 : x^2 = 25 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
        sq_nonneg (x + 5), sq_nonneg (y + 6), sq_nonneg (z + 8)]
  have h5 : x = 5 ∨ x = -5 := by
    have h6 : x^2 = 25 := h4
    have h7 : x = 5 ∨ x = -5 := by
      have h8 : x^2 - 25 = 0 := by linarith
      have h9 : (x - 5) * (x + 5) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- x - 5 = 0
        left
        linarith
      · -- x + 5 = 0
        right
        linarith
    tauto
  cases h5 with
  | inl hx5 =>
    have hx5 : x = 5 := hx5
    have hy6 : y = 6 := by
      rw [hx5] at h1 h2 h3
      nlinarith [sq_nonneg (y - 6), sq_nonneg (z - 8)]
    have hz8 : z = 8 := by
      rw [hx5] at h1 h2 h3
      nlinarith [sq_nonneg (y - 6), sq_nonneg (z - 8)]
    simp [hx5, hy6, hz8]
  | inr hx_neg5 =>
    have hx_neg5 : x = -5 := hx_neg5
    have hy_neg6 : y = -6 := by
      rw [hx_neg5] at h1 h2 h3
      nlinarith [sq_nonneg (y + 6), sq_nonneg (z + 8)]
    have hz_neg8 : z = -8 := by
      rw [hx_neg5] at h1 h2 h3
      nlinarith [sq_nonneg (y + 6), sq_nonneg (z + 8)]
    simp [hx_neg5, hy_neg6, hz_neg8]