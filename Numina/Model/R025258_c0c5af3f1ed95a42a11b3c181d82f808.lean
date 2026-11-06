import Mathlib

theorem algebra_148183 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃ x1 x2 x3 x4 : ℝ, x1 ≠ x2 ∧ x3 ≠ x4 ∧ x1 ≠ x3 ∧ x2 ≠ x4 ∧
      a * x1^2 - 2 = 0 ∧ a * x2^2 - 2 = 0 ∧ 4 - b * x3^2 = 0 ∧ 4 - b * x4^2 = 0 ∧
      (x3 - x1) * (x4 - x2) / 2 = 12) :
    a + b = 1.5 := by
  rcases h with ⟨x1, x2, x3, x4, hx12, hx34, hx13, hx24, h1, h2, h3, h4, h5⟩
  have h1' : a * x1^2 = 2 := by linarith
  have h2' : a * x2^2 = 2 := by linarith
  have h3' : b * x3^2 = 4 := by linarith
  have h4' : b * x4^2 = 4 := by linarith
  have h5' : x1^2 = x2^2 := by
    have h : a * x1^2 = a * x2^2 := by
      linarith
    have h6 : x1^2 = x2^2 := by
      apply (mul_left_inj' ha).mp
      linarith
    linarith
  have h6' : x3^2 = x4^2 := by
    have h : b * x3^2 = b * x4^2 := by
      linarith
    have h7 : x3^2 = x4^2 := by
      apply (mul_left_inj' hb).mp
      linarith
    linarith
  have h7 : x1 = -x2 := by
    have h8 : x1^2 = x2^2 := h5'
    have h9 : (x1 - x2) * (x1 + x2) = 0 := by
      linarith [h8]
    cases' (mul_eq_zero.1 h9) with h9 h10
    · -- x1 - x2 = 0, so x1 = x2, contradiction.
      exfalso
      apply hx12
      linarith
    · -- x1 + x2 = 0, so x1 = -x2.
      linarith
  have h8 : x3 = -x4 := by
    have h9 : x3^2 = x4^2 := h6'
    have h10 : (x3 - x4) * (x3 + x4) = 0 := by
      linarith [h9]
    cases' (mul_eq_zero.1 h10) with h10 h11
    · -- x3 - x4 = 0, so x3 = x4, contradiction.
      exfalso
      apply hx34
      linarith
    · -- x3 + x4 = 0, so x3 = -x4.
      linarith
  have h10 : (x3 - x1) ^ 2 = -24 := by
    have h11 : x4 = -x3 := by
      linarith [h8]
    have h12 : x2 = -x1 := by
      linarith [h7]
    rw [show x4 = -x3 by linarith [h8]] at h5
    rw [show x2 = -x1 by linarith [h7]] at h5
    nlinarith
  nlinarith [sq_nonneg (x3 - x1)]