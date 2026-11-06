import Mathlib

theorem algebra_165476 (x : ℝ) (hx : x ≠ -1 ∧ x ≠ 2) :
    (x ^ 2 + 1) / (x + 1) + (x ^ 2 + 2) / (x - 2) = -2 ↔ x = 1 := by
  constructor
  · -- Forward direction: equation implies x = 1
    intro h
    have h1 : x + 1 ≠ 0 := by
      intro h2
      apply hx.left
      linarith
    have h2 : x - 2 ≠ 0 := by
      intro h3
      apply hx.right
      linarith
    have eq1 : (x ^ 2 + 1) / (x + 1) + (x ^ 2 + 2) / (x - 2) = -2 := h
    have eq2 : (x ^ 2 + 1) * (x - 2) + (x ^ 2 + 2) * (x + 1) = -2 * (x + 1) * (x - 2) := by
      have eq3 : (x + 1) ≠ 0 := h1
      have eq4 : (x - 2) ≠ 0 := h2
      field_simp [eq3, eq4] at eq1 ⊢
      linarith
    have eq3 : 2 * x ^ 3 + x ^ 2 + x - 4 = 0 := by
      ring_nf at eq2 ⊢
      linarith
    have h3 : (x - 1) * (2 * x ^ 2 + 3 * x + 4) = 0 := by
      ring_nf at eq3 ⊢
      linarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where x - 1 = 0, so x = 1
      linarith
    · -- Case where 2x^2 + 3x + 4 = 0, show that it is impossible in reals
      have h6 : 2 * x ^ 2 + 3 * x + 4 = 0 := h5
      nlinarith [sq_nonneg (x + 3 / 4)]
  · -- Backward direction: x = 1 implies equation
    intro h
    rw [h]
    norm_num