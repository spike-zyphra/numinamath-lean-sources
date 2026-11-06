import Mathlib

open Real

theorem inequalities_230508 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 1) :
    a + b + c + 1 / (a * b * c) ≥ 4 * sqrt 3 := by

  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : (a + b + c)^2 ≤ 3 := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]

  have h3 : a + b + c ≤ Real.sqrt 3 := by
    have h4 : (a + b + c) ^ 2 ≤ 3 := h2
    have h5 : (a + b + c) ≤ Real.sqrt 3 := by
      have h6 : Real.sqrt 3 ≥ 0 := by positivity
      have h7 : (a + b + c) ^ 2 ≤ (Real.sqrt 3) ^ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      nlinarith [Real.sqrt_nonneg 3, sq_nonneg (a + b + c)]
    exact h5

  have h4 : a + b + c + 1 / (a * b * c) - 4 * Real.sqrt 3 ≥ 0 := by
    have h5 : 0 < a * b * c := h1
    have h6 : a + b + c + 1 / (a * b * c) - 4 * Real.sqrt 3 ≥ 0 := by
      have h7 : a * b * c > 0 := h1
      have h8 : a + b + c + 1 / (a * b * c) - 4 * Real.sqrt 3 =
          ( (a + b + c) * (a * b * c) + 1 - 4 * Real.sqrt 3 * (a * b * c) ) / (a * b * c) := by
        field_simp
        <;> ring
      rw [h8]
      have h9 : ( (a + b + c) * (a * b * c) + 1 - 4 * Real.sqrt 3 * (a * b * c) ) ≥ 0 := by
        nlinarith [sq_nonneg (a + b + c - Real.sqrt 3), sq_nonneg (a * b * c - 1 / (3 * Real.sqrt 3)), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 3), sq_nonneg (a * b * c * 3 * Real.sqrt 3 - 1), sq_nonneg (a + b + c - 3 * (a * b * c)^(1/3 : ℝ)), h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h10 : (a * b * c) > 0 := h1
      have h11 : ( (a + b + c) * (a * b * c) + 1 - 4 * Real.sqrt 3 * (a * b * c) ) / (a * b * c) ≥ 0 := by
        apply div_nonneg
        linarith [h9]
        linarith [h1]
      linarith
    linarith

  linarith [h4]