import Mathlib

theorem number_theory_7235 (x y z w d : ℤ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hw : w > 0)
    (h1 : y = x + d) (h2 : z = y + d) (h3 : w = z + d) (h4 : x^3 + y^3 + z^3 = w^3) :
    x = 3 * d ∧ y = 4 * d ∧ z = 5 * d ∧ w = 6 * d := by
  have eq1 : y = x + d := h1
  have eq2 : z = x + 2 * d := by
    rw [h2, h1]
    ring
  have eq3 : w = x + 3 * d := by
    rw [h3, h2, h1]
    ring
  rw [eq1, eq2, eq3] at h4
  have eq4 : x ^ 3 - 6 * x * d ^ 2 - 9 * d ^ 3 = 0 := by
    nlinarith
  have hx_eq : x = 3 * d := by
    have eq5 : x ^ 3 - 6 * x * d ^ 2 - 9 * d ^ 3 = 0 := eq4
    have h6 : (x - 3 * d) * (x ^ 2 + 3 * x * d + 3 * d ^ 2) = 0 := by
      nlinarith [sq_nonneg (x - 3 * d), sq_nonneg (d), sq_nonneg (x * d), sq_nonneg (x ^ 2 - 3 * d ^ 2)]
    cases (mul_eq_zero.1 h6) with
    | inl h9 =>
      linarith
    | inr h9 =>
      by_contra h
      push_neg at h
      have h6 : d ≠ 0 := by
        by_contra h10
        rw [show d = 0 by linarith [h10]] at h9
        nlinarith [sq_nonneg (x * d), sq_nonneg (d * 2), sq_nonneg (x ^ 2 - 3 * d ^ 2)]
      have h7 : (x * 2 + 3 * d) ^ 2 = ( -3 * d ^ 2 * 4 ) := by
        nlinarith
      have sq_pos : (x * 2 + 3 * d) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (x * 2 + 3 * d)]
      nlinarith [show (d ^ 2 : ℤ) > 0 by apply sq_pos_of_ne_zero (show d ≠ 0 by exact h6)]
  have eq6 : y = 4 * d := by
    rw [show x = 3 * d by linarith [hx_eq]] at h1
    linarith
  have eq7 : z = 5 * d := by
    have h5 : z = x + 2 * d := by
      rw [h2, h1]
      ring
    rw [show x = 3 * d by linarith [hx_eq]] at h5
    linarith
  have eq8 : w = 6 * d := by
    have h7 : w = x + 3 * d := by
      rw [h3, h2, h1]
      ring
    rw [show x = 3 * d by linarith [hx_eq]] at h7
    linarith
  constructor
  · exact hx_eq
  constructor
  · exact eq6
  constructor
  · exact eq7
  · exact eq8