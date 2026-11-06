import Mathlib

theorem algebra_213565 {a b c : ℝ} (h₀ : a ≠ 0) (h₁ : b ≠ 0) (h₂ : c ≠ 0)
    (h₃ : a * b * c = 1) (h₄ : a + b + c = 1 / a + 1 / b + 1 / c) :
    a = 1 ∨ b = 1 ∨ c = 1 := by
  have eq1 : 1 / a + 1 / b + 1 / c = b * c + a * c + a * b := by
    have h5 : 1 / a = b * c := by
      have h6 : a * b * c = 1 := h₃
      have : 1 / a = (b * c) := by
        field_simp [h₀]
        nlinarith
      linarith
    have h5' : 1 / b = a * c := by
      have h6 : a * b * c = 1 := h₃
      have : 1 / b = (a * c) := by
        field_simp [h₁]
        nlinarith
      linarith
    have h5'' : 1 / c = a * b := by
      have h6 : a * b * c = 1 := h₃
      have : 1 / c = (a * b) := by
        field_simp [h₂]
        nlinarith
      linarith
    linarith [h5, h5', h5'']
  have eq2 : a + b + c = b * c + a * c + a * b := by
    linarith [h₄, eq1]
  have eq3 : (a - 1) * (b - 1) * (c - 1) = 0 := by
    have h6 : a * b * c = 1 := h₃
    nlinarith [sq_nonneg (a * b - a * c), sq_nonneg (a * b - b * c), sq_nonneg (a * c - b * c), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), eq2, h6]
  cases' (mul_eq_zero.mp eq3) with eq4 eq5
  cases' (mul_eq_zero.mp eq4) with eq6 eq7
  · -- Case `a - 1 = 0` implies `a = 1`
    left
    linarith
  · -- Case `b - 1 = 0` implies `b = 1`
    right
    left
    linarith
  · -- Case `c - 1 = 0` implies `c = 1`
    right
    right
    linarith