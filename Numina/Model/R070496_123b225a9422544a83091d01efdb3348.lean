import Mathlib

theorem algebra_312300 (a b c : ℤ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : a ≠ c) :
    3 * a^2 + 2 * b^2 + 4 * c^2 - a * b - 3 * b * c - 5 * c * a ≥ 6 := by

  have h5 : a - b ≠ 0 := by
    intro h
    apply h₀
    linarith
  have h6 : b - c ≠ 0 := by
    intro h
    apply h₁
    linarith
  have h7 : a - c ≠ 0 := by
    intro h
    apply h₂
    linarith

  have h8 : (a - b) ^ 2 ≥ 1 := by
    have h9 : (a - b) ≠ 0 := h5
    have h10 : (a - b) ^ 2 ≥ 1 := by
      by_contra h
      push_neg at h
      have h11 : (a - b) ^ 2 < 1 := by linarith
      have h12 : (a - b) ^ 2 ≥ 0 := by apply sq_nonneg
      have h13 : (a - b) ^ 2 = 0 := by
        linarith
      have h14 : a - b = 0 := by
        rw [sq_eq_zero_iff] at h13
        exact h13
      contradiction
    linarith

  have h9 : (b - c) ^ 2 ≥ 1 := by
    have h10 : (b - c) ≠ 0 := h6
    have h11 : (b - c) ^ 2 ≥ 1 := by
      by_contra h
      push_neg at h
      have h12 : (b - c) ^ 2 < 1 := by linarith
      have h13 : (b - c) ^ 2 ≥ 0 := by apply sq_nonneg
      have h14 : (b - c) ^ 2 = 0 := by
        linarith
      have h15 : b - c = 0 := by
        rw [sq_eq_zero_iff] at h14
        exact h14
      contradiction
    linarith

  have h10 : (a - c) ^ 2 ≥ 1 := by
    have h11 : (a - c) ≠ 0 := h7
    have h12 : (a - c) ^ 2 ≥ 1 := by
      by_contra h
      push_neg at h
      have h13 : (a - c) ^ 2 < 1 := by linarith
      have h14 : (a - c) ^ 2 ≥ 0 := by apply sq_nonneg
      have h15 : (a - c) ^ 2 = 0 := by
        linarith
      have h16 : a - c = 0 := by
        rw [sq_eq_zero_iff] at h15
        exact h15
      contradiction
    linarith

  nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c), sq_nonneg (a + 1), sq_nonneg (b + 1), sq_nonneg (c - 1), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c), h8, h9, h10]