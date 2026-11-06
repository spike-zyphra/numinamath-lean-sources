import Mathlib

theorem algebra_264978 (a : ℝ) (h : ∃ x y, x ≠ y ∧ x^2 - a * x + a + 2 = 0 ∧ y^2 - a * y + a + 2 = 0 ∧
    x^3 + y^3 = -8) : a = -2 := by
  rcases h with ⟨x, y, hne, hx, hy, hsum⟩
  have h1 : x + y = a := by
    have h2 : x ^ 2 - a * x + a + 2 - (y ^ 2 - a * y + a + 2) = 0 := by linarith [hx, hy]
    have h3 : (x - y) * (x + y - a) = 0 := by
      nlinarith
    cases (mul_eq_zero.1 h3) with
    | inl h4 =>
      exfalso
      exact hne (by linarith)
    | inr h5 =>
      linarith

  have h2 : x * y = a + 2 := by
    have eq1 : x ^ 2 + y ^ 2 = a ^ 2 - 2 * a - 4 := by
      nlinarith [hx, hy, h1]
    have eq2 : x * y = ( (x + y) ^ 2 - (x ^ 2 + y ^ 2) ) / 2 := by
      ring
    rw [eq1, h1] at eq2
    nlinarith

  have eq3 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
    ring
  rw [eq3, h1, h2] at hsum
  have h3 : a ^ 3 - 3 * a ^ 2 - 6 * a + 8 = 0 := by
    nlinarith
  have h4 : (a + 2) * (a - 1) * (a - 4) = 0 := by
    nlinarith [sq_nonneg (a ^ 2), sq_nonneg (a - 2), sq_nonneg (a - 4)]
  cases' (mul_eq_zero.1 h4) with h5 h6
  cases' (mul_eq_zero.1 h5) with h7 h8
  · -- Case a + 2 = 0, so a = -2
    linarith
  · -- Case a - 1 = 0, so a = 1
    have h11 : a = (1 : ℝ) := by linarith
    have h5 : x ^ 2 - a * x + a + 2 = 0 := hx
    rw [show a = (1 : ℝ) by linarith] at h5
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 1), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h'
      apply hne
      linarith
    )
    ]
  · -- Case a - 4 = 0, so a = 4
    have h11 : a = (4 : ℝ) := by linarith
    have h5 : x ^ 2 - a * x + a + 2 = 0 := hx
    rw [show a = (4 : ℝ) by linarith] at h5
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 4), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h'
      apply hne
      linarith
    )
    ]