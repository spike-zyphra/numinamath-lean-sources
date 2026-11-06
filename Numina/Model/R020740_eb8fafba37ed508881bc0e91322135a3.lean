import Mathlib

theorem algebra_116802 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 2 * c > a + b) :
    c - Real.sqrt (c^2 - a * b) < a ∧ a < c + Real.sqrt (c^2 - a * b) := by
  have h1 : 0 < a * b := mul_pos ha hb
  have h3 : c ^ 2 ≥ a * b := by
    nlinarith [sq_nonneg (c - (a + b) / 2), sq_nonneg (a - b), sq_nonneg (c - a - b / 2), sq_nonneg (a + b - 2 * c), sq_nonneg (a - c), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h3' : c ^ 2 - a * b ≥ 0 := by
    nlinarith [sq_nonneg (c - (a + b) / 2), sq_nonneg (a - b), sq_nonneg (c - a - b / 2), sq_nonneg (a + b - 2 * c), sq_nonneg (a - c), sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, h, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h4 : c - Real.sqrt (c^2 - a * b) < a := by
    have h_sq_pos : a + b < 2 * c := by linarith
    have h5 : Real.sqrt (c ^ 2 - a * b) ≥ 0 := Real.sqrt_nonneg (c ^ 2 - a * b)
    by_cases h7 : c - Real.sqrt (c^2 - a * b) < a
    · exact h7
    · -- Assume ¬(c - Real.sqrt (c^2 - a * b) < a)
      push_neg at h7
      have h8 : c - Real.sqrt (c^2 - a * b) ≥ a := h7
      have h11 : c - a ≥ Real.sqrt (c ^ 2 - a * b) := by linarith [h7]
      have h9 : c - a ≥ 0 := by
        nlinarith [h, sq_nonneg (a - c), sq_nonneg (c - a - b / 2), sq_nonneg (a - b), sq_nonneg (a + b - 2 * c), sq_nonneg (c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h10 : Real.sqrt (c ^ 2 - a * b) ≥ 0 := Real.sqrt_nonneg (c^2 - a * b)
      have h12 : (c - a) ^ 2 ≥ (Real.sqrt (c ^ 2 - a * b)) ^ 2 := by nlinarith [h11, Real.sqrt_nonneg (c^2 - a * b)]
      have h14 : (Real.sqrt (c ^ 2 - a * b)) ^ 2 = c^2 - a * b := Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg (a - b), sq_nonneg (c - a - b / 2), sq_nonneg (a + b - 2 * c), sq_nonneg (a - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  have h5 : a < c + Real.sqrt (c^2 - a * b) := by
    have h6 : Real.sqrt (c ^ 2 - a * b) ≥ 0 := Real.sqrt_nonneg (c^2 - a * b)
    by_cases h8 : a < c + Real.sqrt (c^2 - a * b)
    · exact h8
    · -- Assume ¬(a < c + Real.sqrt (c^2 - a * b))
      push_neg at h8
      have h7 : a - c ≥ Real.sqrt (c ^ 2 - a * b) := by linarith
      have h8 : a - c ≥ 0 := by
        nlinarith [h7, Real.sqrt_nonneg (c ^ 2 - a * b)]
      have h9 : (a - c) ^ 2 ≥ (Real.sqrt (c ^ 2 - a * b)) ^ 2 := by nlinarith [h7, Real.sqrt_nonneg (c^2 - a * b)]
      have h14 : (Real.sqrt (c ^ 2 - a * b)) ^ 2 = c^2 - a * b := Real.sq_sqrt (by linarith)
      nlinarith [sq_nonneg (a - b), sq_nonneg (c - (a + b) / 2), sq_nonneg (a - c), sq_nonneg (a + b - 2 * c), sq_nonneg (c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  constructor
  · exact h4
  · exact h5