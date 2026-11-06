import Mathlib

theorem algebra_96280 (x : ℝ) (hx : x ≠ 0) : (7 * x) ^ 14 = (14 * x) ^ 7 ↔ x = 2 / 7 := by
  constructor
  · -- Assume $(7 * x)^{14} = (14 * x)^7$ and prove $x = 2/7$.
    intro h
    have h1 : (7 * x) ^ 14 = (14 * x) ^ 7 := h
    have h2 : (14 * x) ^ 7 = 2 ^ 7 * (7 * x) ^ 7 := by
      ring_nf
    rw [h2] at h1
    have h3 : ((7 * x) ^ 7) * ((7 * x) ^ 7 - 2 ^ 7) = 0 := by
      nlinarith [sq_nonneg ((7 * x) ^ 7 - 2 ^ 7), sq_nonneg ((7 * x) ^ 7), sq_nonneg (7 * x - 2), sq_pos_of_ne_zero hx]
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case h4: (7 * x) ^ 7 = 0
      have h6 : (7 * x) ^ 7 = 0 := by
        linarith
      have h7 : 7 * x = 0 := by
        have h8 : (7 * x) ^ 7 = 0 := h6
        have h9 : 7 * x = 0 := by
          have h10 : (7 * x) ^ 7 = 0 := h6
          simp at h10 ⊢
          all_goals nlinarith
        linarith
      have h10 : x = 0 := by
        linarith
      contradiction
    · -- Case h5: (7 * x) ^ 7 - 2 ^ 7 = 0
      have h8 : (7 * x) ^ 7 = 2 ^ 7 := by
        linarith
      have h10 : 7 * x = 2 := by
        have h11 : (7 * x) ^ 7 - (2 : ℝ) ^ 7 = 0 := by
          linarith
        have h12 : (7 * x - 2) * ((7 * x) ^ 6 + (7 * x) ^ 5 * (2 : ℝ) + (7 * x) ^ 4 * (2 : ℝ) ^ 2 + (7 * x) ^ 3 * (2 : ℝ) ^ 3 + (7 * x) ^ 2 * (2 : ℝ) ^ 4 + (7 * x) * (2 : ℝ) ^ 5 + (2 : ℝ) ^ 6) = 0 := by
          ring_nf at h11 ⊢
          <;> nlinarith
        cases' (mul_eq_zero.mp h12) with h13 h14
        · -- Case where 7 * x - 2 = 0, hence 7 * x = 2
          linarith
        · -- Case where the sum is zero
          nlinarith [sq_nonneg ((7 * x) ^ 3), sq_nonneg ((7 * x) ^ 2), sq_nonneg ((7 * x) ^ 1), sq_nonneg ((7 * x) ^ 0), sq_nonneg ((7 * x - 2) ^ 2), sq_nonneg ((7 * x - 2) ^ 1), sq_nonneg ((2:ℝ)^2), sq_nonneg ((2:ℝ)^1), sq_nonneg ((2:ℝ)^0)]
      have h11 : x = 2 / 7 := by
        linarith
      exact h11
  · -- Assume x = 2/7 and prove (7 * x)^14 = (14 * x)^7.
    intro h
    rw [h]
    norm_num