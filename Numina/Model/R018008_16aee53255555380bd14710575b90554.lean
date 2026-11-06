import Mathlib

theorem algebra_204911 {a b c r : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h1 : a * (b - c) / (b * (c - a)) = r) (h2 : b * (c - a) / (c * (b - a)) = r)
    (hr : r > 0) : r = (Real.sqrt 5 - 1) / 2 := by

  have h3 : b ≠ 0 := by
    by_contra h
    rw [h] at h1
    have h1' : a * (0 - c) / (0 * (c - a)) = r := by
      simpa using h1
    have h4 : a * (0 - c) / (0 * (c - a)) = 0 := by
      rw [show 0 * (c - a) = (0 : ℝ) by ring]
      norm_num
    rw [h4] at h1'
    linarith

  have h4 : c ≠ 0 := by
    by_contra h
    rw [h] at h2
    have h2' : b * (0 - a) / (0 * (b - a)) = r := by
      simpa using h2
    have h5 : 0 * (b - a) = (0 : ℝ) := by ring
    rw [h5] at h2'
    have h7 : b * (0 - a) / (0 : ℝ) = 0 := by
      simp
    rw [h7] at h2'
    linarith

  have h5 : c - a ≠ 0 := by
    intro h
    apply hc
    have : a = c := by linarith
    tauto

  have h6 : b - a ≠ 0 := by
    intro h
    apply ha
    have : a = b := by linarith
    tauto

  have eq1 : a * (b - c) = r * (b * (c - a)) := by
    have h7 : b * (c - a) ≠ 0 := by
      apply mul_ne_zero
      · exact h3
      · exact h5
    have h8 : a * (b - c) / (b * (c - a)) = r := h1
    field_simp at h8 ⊢
    nlinarith

  have eq2 : b * (c - a) = r * (c * (b - a)) := by
    have h10 : c * (b - a) ≠ 0 := by
      apply mul_ne_zero
      · exact h4
      · exact h6
    have h11 : b * (c - a) / (c * (b - a)) = r := by
      linarith [h2]
    field_simp at h11 ⊢
    nlinarith

  -- Now, we need to solve r from these equations.
  have h7 : r ^ 2 + r - 1 = 0 := by
    apply (mul_left_inj' (show b ≠ 0 by exact h3)).mp
    apply (mul_left_inj' (show (c - a) ≠ 0 by exact h5)).mp
    nlinarith [sq_pos_of_ne_zero (show b ≠ 0 by exact h3), sq_pos_of_ne_zero (show c - a ≠ 0 by exact h5), sq_pos_of_pos hr]

  have h2r : r ^ 2 + r - 1 = 0 := h7

  have h10 : r = (Real.sqrt 5 - 1) / 2 := by
    have h14 : r ^ 2 + r - 1 = 0 := h2r
    have h15 : (r - (Real.sqrt 5 - 1) / 2) * (r + (Real.sqrt 5 + 1) / 2) = 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
    cases' (mul_eq_zero.mp h15) with h16 h17
    · -- r = (Real.sqrt 5 - 1) / 2
      linarith
    · -- r = - (Real.sqrt 5 + 1) / 2
      have h18 : r < 0 := by
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by linarith)]
      linarith
  linarith