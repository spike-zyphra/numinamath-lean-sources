import Mathlib

open Real

theorem algebra_208948 {x : ℝ} (hx : x ≠ 0) :
    ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3) - 3) / ((x + 1 / x) ^ 2 - (x ^ 2 + 1 / x ^ 2) + 1) > 1 ↔
    x > 0 ∧ x ≠ 1 := by
  have h1 : (x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3) - 3 = 3 * ((x + 1 / x) - 1) := by
    field_simp [hx]
    ring
  have h2 : (x + 1 / x) ^ 2 - (x ^ 2 + 1 / x ^ 2) + 1 = 3 := by
    field_simp [hx]
    ring
  have h3 : ((x + 1 / x) ^ 3 - (x ^ 3 + 1 / x ^ 3) - 3) / ((x + 1 / x) ^ 2 - (x ^ 2 + 1 / x ^ 2) + 1) = (x + 1 / x) - 1 := by
    rw [h1, h2]
    field_simp [show (3 : ℝ) ≠ 0 by norm_num]
    <;> ring_nf <;> norm_num
  rw [h3]
  constructor
  · -- Assume (x + 1/x) - 1 > 1, prove x > 0 ∧ x ≠ 1
    intro h
    have h' : x + 1/x - 2 > 0 := by linarith
    have h1 : x > 0 := by
      by_contra h2
      push_neg at h2
      have h3 : x < 0 := by
        by_contra h4
        have h5 : x ≥ 0 := by linarith
        have h6 : x = 0 := by linarith [show x = 0 from by linarith]
        contradiction
      have h4 : x + (1 / x) - 2 > 0 := by linarith
      have h6 : x < 0 := h3
      have h7 : (x) * ((x + 1 / x) - 2) < 0 := by nlinarith
      have h8 : (x)^2 + 1 + (-2 * x) < 0 := by
        have h9 : (x) * ((x + 1 / x) - 2) < 0 := by nlinarith
        have h10 : (x) * ((x + 1 / x) - 2) = (x)^2 + 1 + (-2 * x) := by
          field_simp [show x ≠ 0 by assumption]
          ring
        linarith [h10]
      nlinarith [sq_nonneg (x - 1)]
    have h2 : x ≠ 1 := by
      by_contra h4
      rw [h4] at h'
      norm_num at h'
    constructor
    · exact h1
    · exact h2
  · -- Assume x > 0 ∧ x ≠ 1, prove (x + 1/x) - 1 > 1
    intro h
    have h1 : x > 0 := h.1
    have h2 : x ≠ 1 := h.2
    have h3 : x + 1/x - 2 > 0 := by
      have h4 : x + 1/x - 2 > 0 := by
        have h5 : x > 0 := h1
        have h6 : x ≠ 1 := h2
        have h7 : x + (1 / x) > 2 := by
          have h8 : x * (1 / x) = 1 := by 
            field_simp [show x ≠ 0 by assumption]
          nlinarith [sq_nonneg (x - 1), sq_pos_of_ne_zero (show x - 1 ≠ 0 by intro h9; apply h2; linarith), sq_nonneg (x + 1)]
        nlinarith
      linarith
    linarith