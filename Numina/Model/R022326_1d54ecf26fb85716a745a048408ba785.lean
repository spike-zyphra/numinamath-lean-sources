import Mathlib

theorem algebra_176787 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a + b + c = 0) (h2 : a ^ 4 + b ^ 4 + c ^ 4 = 128) :
    a * b + b * c + c * a = -8 := by

  have h1_sq : a ^ 2 + b ^ 2 + c ^ 2 = -2 * (a * b + b * c + c * a) := by
    have h : a + b + c = 0 := h1
    have h_sq : (a + b + c) ^ 2 = 0 := by
      rw [h]
      norm_num
    nlinarith

  have h3 : a ^ 4 + b ^ 4 + c ^ 4 = (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 - 2 * ((a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2) := by
    ring

  have h4 : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 = (a * b + b * c + c * a) ^ 2 - 2 * (a * b * (b * c) + b * c * (c * a) + c * a * (a * b)) := by
    ring

  have h5 : a * b * (b * c) + b * c * (c * a) + c * a * (a * b) = 0 := by
    have h_zero : a + b + c = 0 := h1
    have h6 : a * b * (b * c) + b * c * (c * a) + c * a * (a * b) = (a * b * c) * (a + b + c) := by
      ring_nf
    rw [h6, h_zero]
    norm_num

  have h7 : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 = (a * b + b * c + c * a) ^ 2 := by
    rw [h4, h5]
    all_goals linarith


  have h3' : a ^ 4 + b ^ 4 + c ^ 4 = 2 * (a * b + b * c + c * a) ^ 2 := by
    rw [h3, h7]
    nlinarith [h1_sq]

  have h8 : (a * b + b * c + c * a) ^ 2 = 64 := by
    nlinarith [h3', h2]

  have h9 : a * b + b * c + c * a = 8 ∨ a * b + b * c + c * a = -8 := by
    have h : (a * b + b * c + c * a) ^ 2 - 64 = 0 := by
      linarith [h8]
    have h10 : (a * b + b * c + c * a - 8) * (a * b + b * c + c * a + 8) = 0 := by
      nlinarith [h]
    cases (mul_eq_zero.1 h10) with
    | inl h11 =>
      left
      linarith
    | inr h12 =>
      right
      linarith

  rcases h9 with h9 | h9
  · -- Assume $a * b + b * c + c * a = 8$, which would be contradictory.
    nlinarith [sq_nonneg (a ^ 2 + b ^ 2 + c ^ 2), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), h1_sq, h9]
  · -- The only possible value
    exact h9