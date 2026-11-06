import Mathlib

theorem algebra_14481 {r : ℝ} (rne1 : r - 1 ≠ 0)(rne5 : r - 5 ≠ 0):
(r^2 - 5 * r + 4) / (r^2 - 8 * r + 7) = (r^2 - 2 * r - 15) / (r^2 - r - 20) ↔
r = -5 / 4 := by
  constructor
  · -- Assume the equality holds, prove r = -5/4
    intro h
    have h1 : r^2 - 8 * r + 7 ≠ 0 := by
      by_contra h1
      have h2 : r ^ 2 - 8 * r + 7 = 0 := by linarith
      have h3 : r = 1 ∨ r = 7 := by 
        have h4 : r ^ 2 - 8 * r + 7 = 0 := h2
        have : (r - 1) * (r - 7) = 0 := by linarith
        cases' (mul_eq_zero.1 this) with h5 h6
        · -- r - 1 = 0, so r = 1
          left
          linarith
        · -- r - 7 = 0, so r = 7
          right
          linarith
      cases h3 with
      | inl h4 =>
        exfalso
        apply rne1
        linarith
      | inr h4 =>
        have h5 : r = 7 := by linarith
        rw [h5] at h
        norm_num [h5] at h
    have h2 : r^2 - r - 20 ≠ 0 := by
      by_contra h2
      have h4 : r ^ 2 - r - 20 = 0 := by linarith
      have h5 : r = 5 ∨ r = -4 := by 
        have h6 : r ^ 2 - r - 20 = 0 := h4
        have : (r - 5) * (r + 4) = 0 := by linarith
        cases' (mul_eq_zero.1 this) with h7 h8
        · -- r - 5 = 0, so r = 5
          left
          linarith
        · -- r + 4 = 0, so r = -4
          right
          linarith
      cases h5 with
      | inl h6 =>
        exfalso
        apply rne5
        linarith
      | inr h6 =>
        have h7 : r = -4 := by linarith
        rw [h7] at h
        norm_num [h7] at h
    have h3 : (r^2 - 5 * r + 4) * (r^2 - r - 20) = (r^2 - 2 * r - 15) * (r^2 - 8 * r + 7) := by
      field_simp [h1, h2] at h ⊢
      nlinarith
    have h4 : 4 * r ^ 3 - 19 * r ^ 2 - 10 * r + 25 = 0 := by
      nlinarith [h3]
    have h5 : (r + 5 / 4) * (4 * r ^ 2 - 24 * r + 20) = 0 := by 
      nlinarith [h4]
    cases' (mul_eq_zero.1 h5) with h6 h7
    · -- Case h6 : r + 5/4 = 0, so r = -5/4
      linarith
    · -- Case h7 : 4 * r^2 - 24 * r + 20 = 0
      have h8 : 4 * r ^ 2 - 24 * r + 20 = 0 := by linarith
      have h9 : (r - 1) * (r - 5) = 0 := by 
        nlinarith [h8]
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- Case h10 : r - 1 = 0, so r = 1
        exfalso
        apply rne1
        linarith
      · -- Case h11 : r - 5 = 0, so r = 5
        exfalso
        apply rne5
        linarith
  · -- Show r = -5/4 implies equality
    intro h
    rw [h]
    norm_num