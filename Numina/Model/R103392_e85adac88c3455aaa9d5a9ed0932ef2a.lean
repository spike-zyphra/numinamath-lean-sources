import Mathlib

theorem algebra_199359 (x : ℝ) (hx : x^3 = 2 + Real.sqrt 5) :
    x = (1 + Real.sqrt 5) / 2 := by
  have h1 : x^3 = 2 + Real.sqrt 5 := hx
  have h2 : ((1 + Real.sqrt 5) / 2) ^ 3 = 2 + Real.sqrt 5 := by
    ring_nf
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
    have h6 : Real.sqrt 5 ^ 3 = Real.sqrt 5 * 5 := by
      calc
        Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
        _ = 5 * Real.sqrt 5 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
        _ = Real.sqrt 5 * 5 := by ring
    nlinarith [Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num : (5 : ℝ) > 0), h5, h6]
  have h3 : x ^ 3 = ((1 + Real.sqrt 5) / 2) ^ 3 := by
    rw [h1]
    rw [h2]
  have h4 : x = (1 + Real.sqrt 5) / 2 := by
    have h5 : x ^ 3 - ((1 + Real.sqrt 5) / 2) ^ 3 = 0 := by
      linarith [h3]
    have h6 : (x - (1 + Real.sqrt 5) / 2) * (x ^ 2 + x * ((1 + Real.sqrt 5) / 2) + ((1 + Real.sqrt 5) / 2) ^ 2) = 0 := by
      ring_nf at h5 ⊢
      <;> nlinarith
    cases' (mul_eq_zero.1 h6) with h7 h8
    · linarith
    · -- Show that the quadratic factor is always positive
      have h9 : x ^ 2 + x * ((1 + Real.sqrt 5) / 2) + ((1 + Real.sqrt 5) / 2) ^ 2 > 0 := by
        nlinarith [sq_pos_of_pos (show 0 < Real.sqrt 5 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (x + (1 + Real.sqrt 5) / 4)]
      nlinarith [h9]
  exact h4