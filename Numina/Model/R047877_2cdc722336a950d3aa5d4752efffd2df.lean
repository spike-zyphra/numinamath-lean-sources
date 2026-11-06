import Mathlib

theorem algebra_235496 (x : ℝ) (hx : x ≠ 0) :
    Real.sqrt (3 - 1 / (2020 * x)) = 1 - 1 / (2020 * x) ↔ x = -1 / 2020 := by
  constructor
  · -- Assume Real.sqrt (3 - 1 / (2020 * x)) = 1 - 1 / (2020 * x), prove x = -1 / 2020
    intro h_eq
    have h1 : 3 - 1 / (2020 * x) ≥ 0 := by
      by_contra h
      push_neg at h
      have h2 : Real.sqrt (3 - 1 / (2020 * x)) = 0 := by
        rw [Real.sqrt_eq_zero']
        all_goals linarith
      have h3 : (1 - 1 / (2020 * x)) = 0 := by
        nlinarith [h_eq, h2]
      have h4 : (1 / (2020 * x)) = 1 := by
        nlinarith
      have h3 : 2020 * x = 1 := by
        have h4 : x ≠ 0 := hx
        field_simp at h4 h4
        all_goals
        linarith
      have h4 : 3 - 1 / (2020 * x) = 2 := by
        rw [show 1 / (2020 * x) = 1 by linarith [h4]]
        linarith
      nlinarith
    have h2 : (1 - 1 / (2020 * x)) ≥ 0 := by
      by_contra h
      push_neg at h
      have h3 : Real.sqrt (3 - 1 / (2020 * x)) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h4 : (1 - 1 / (2020 * x)) < 0 := by
        linarith
      nlinarith [h_eq, h3, h4]
    have h3 : (3 - 1 / (2020 * x)) = (1 - 1 / (2020 * x)) ^ 2 := by
      calc
        3 - 1 / (2020 * x) = (Real.sqrt (3 - 1 / (2020 * x))) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (1 - 1 / (2020 * x)) ^ 2 := by
          rw [h_eq]
    have h4 : (1 / (2020 * x)) = 2 ∨ (1 / (2020 * x)) = -1 := by
      have h5 : (3 - 1 / (2020 * x)) = (1 - 1 / (2020 * x)) ^ 2 := h3
      have h6 : ((1 / (2020 * x))) ^ 2 - (1 / (2020 * x)) - 2 = 0 := by
        nlinarith
      have h7 : ((1 / (2020 * x)) - 2) * ((1 / (2020 * x)) + 1) = 0 := by
        nlinarith [h6]
      cases' (mul_eq_zero.1 h7) with h8 h9
      · -- case h8: (1 / (2020 * x)) - 2 = 0
        left
        linarith
      · -- case h9: (1 / (2020 * x)) + 1 = 0
        right
        linarith
    cases h4 with
    | inl h5 =>
      -- $\frac{1}{2020x} = 2$, then $2020x = \frac{1}{2}$, so $x = \frac{1}{4040}$, which does not satisfy the original equation.
      have h6 : (1 / (2020 * x)) = 2 := h5
      have h7 : 2020 * x = 1 / 2 := by
        have h8 : x ≠ 0 := hx
        field_simp at h6
        nlinarith
      nlinarith [h_eq, Real.sqrt_nonneg (3 - 1 / (2020 * x)), h7]
    | inr h5 =>
      -- $\frac{1}{2020x} = -1$, then $2020x = -1$, so $x = -\frac{1}{2020}$.
      have h6 : (1 / (2020 * x)) = -1 := h5
      have h7 : 2020 * x = -1 := by
        have h8 : x ≠ 0 := hx
        field_simp at h6
        nlinarith
      have h8 : x = -1 / 2020 := by
        linarith
      assumption
  · -- Assume x = -1/2020, prove sqrt(3 - 1/(2020*x)) = 1 - 1/(2020*x)
    intro h_eq
    have h1 : x = -1 / 2020 := by
      linarith
    have h2 : (1 / (2020 * x)) = -1 := by
      rw [show x = -1 / 2020 by linarith]
      norm_num
    have h3 : (3 - 1 / (2020 * x)) = 4 := by
      rw [h2]
      norm_num
    have h4 : (1 - 1 / (2020 * x)) = 2 := by
      rw [h2]
      norm_num
    rw [h3, h4]
    have h5 : Real.sqrt (4 : ℝ) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h5]
    all_goals linarith