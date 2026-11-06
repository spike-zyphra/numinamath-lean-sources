import Mathlib

theorem algebra_106368 (a : ℝ) (h : ∃ x1 x2 x3 : ℝ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    x1^3 - 3 * a * x1^2 + (2 * a^2 + 5) * x1 - 2 * a^2 + 3 = 0 ∧
    x2^3 - 3 * a * x2^2 + (2 * a^2 + 5) * x2 - 2 * a^2 + 3 = 0 ∧
    x3^3 - 3 * a * x3^2 + (2 * a^2 + 5) * x3 - 2 * a^2 + 3 = 0 ∧
    ∃ d : ℝ, x2 = x1 + d ∧ x3 = x2 + d) : a = 3 := by
  rcases h with ⟨x1, x2, x3, hx12, hx23, hx31, h1, h2, h3, ⟨d, h21, h32⟩⟩
  have h4 : x2 = x1 + d := by linarith
  have h5 : x3 = x2 + d := by linarith
  have h6 : x3 = x1 + 2 * d := by
    rw [h5, h4]
    ring
  rw [h4] at h2
  rw [h6] at h3
  have eq1 : d ≠ 0 := by
    by_contra h
    have h7 : x2 = x1 := by
      rw [h4]
      linarith [h]
    have h8 : x1 = x2 := by linarith [h7]
    contradiction
  have eq2 : 3 * x1^2 + 3 * x1 * d + d^2 - 6 * a * x1 - 3 * a * d + 2 * a^2 + 5 = 0 := by
    have h7 : d ≠ 0 := eq1
    have h8 : d * (3 * x1^2 + 3 * x1 * d + d^2 - 6 * a * x1 - 3 * a * d + 2 * a^2 + 5) = 0 := by
      nlinarith
    have h9 : 3 * x1^2 + 3 * x1 * d + d^2 - 6 * a * x1 - 3 * a * d + 2 * a^2 + 5 = 0 := by
      apply (mul_right_inj' h7).mp
      linarith
    linarith
  have eq3 : 6 * x1^2 + 12 * x1 * d + 8 * d^2 - 12 * a * x1 - 12 * a * d + 4 * a^2 + 10 = 0 := by
    have h7 : d ≠ 0 := eq1
    have h8 : d * (6 * x1^2 + 12 * x1 * d + 8 * d^2 - 12 * a * x1 - 12 * a * d + 4 * a^2 + 10) = 0 := by
      nlinarith
    have h9 : 6 * x1^2 + 12 * x1 * d + 8 * d^2 - 12 * a * x1 - 12 * a * d + 4 * a^2 + 10 = 0 := by
      apply (mul_right_inj' h7).mp
      linarith
    linarith
  have eq4 : 2 * a^2 - 5 * a - 3 = 0 := by
    have h7 : d ≠ 0 := eq1
    nlinarith [eq2, eq3, sq_pos_of_ne_zero eq1, sq_nonneg (d * d), sq_nonneg (x1 - a), sq_nonneg (x1 + d - a), sq_nonneg (x1 + 2 * d - a)]
  have h8 : (a - 3) * (2 * a + 1) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h8) with ha1 ha2
  · -- Assume a - 3 = 0
    linarith
  · -- Assume 2 * a + 1 = 0
    have ha2' : a = -1 / 2 := by linarith
    rw [ha2'] at eq2 eq3
    nlinarith [sq_nonneg (d), sq_nonneg (x1), sq_nonneg (x1 + d), sq_nonneg (d^2), sq_nonneg (x1 -d), sq_nonneg (x1 +2*d), sq_nonneg (d -0)]