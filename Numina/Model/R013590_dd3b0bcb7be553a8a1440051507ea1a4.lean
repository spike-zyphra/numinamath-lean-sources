import Mathlib

theorem algebra_225981 (x : ℝ) (hx : x > 1) :
    2 + 3 * x + 4 / (x - 1) ≥ 2 + 3 * (1 + 2 * Real.sqrt 3 / 3) + 4 / ((1 + 2 * Real.sqrt 3 / 3) - 1) := by
  have h1 : x - 1 > 0 := by linarith
  have h2 : (1 + 2 * Real.sqrt 3 / 3) - 1 > 0 := by
    have h4 : Real.sqrt 3 > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    nlinarith [Real.sqrt_nonneg 3]

  have h4 : 2 + 3 * x + 4 / (x - 1) - (2 + 3 * (1 + 2 * Real.sqrt 3 / 3) + 4 / ((1 + 2 * Real.sqrt 3 / 3) - 1)) ≥ 0 := by
    have h5 : (x - 1) > 0 := h1
    have h6 : ( (1 + 2 * Real.sqrt 3 / 3 ) - 1 ) > 0 := h2
    have h7 : 2 + 3 * x + 4 / (x - 1) - (2 + 3 * (1 + 2 * Real.sqrt 3 / 3) + 4 / ((1 + 2 * Real.sqrt 3 / 3) - 1)) =
        3 * (x - 1) + 4 / (x - 1) - 4 * Real.sqrt 3 := by
      have eq1 : ( (1 + 2 * Real.sqrt 3 / 3 ) - 1 ) > 0 := h2
      have eq2 : 4 / ((1 + 2 * Real.sqrt 3 / 3 ) - 1 ) = 2 * Real.sqrt 3 := by
        field_simp
        <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
      rw [eq2]
      field_simp
      <;> ring_nf <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by linarith)]
    rw [h7] at *
    have h7' : 3 * (x - 1) + 4 / (x - 1) - 4 * Real.sqrt 3 ≥ 0 := by
      have h9 : (x - 1) > 0 := h1
      have h10 : 3 * (x - 1) + 4 / (x - 1) - 4 * Real.sqrt 3 =
          (3 * (x - 1) ^ 2 + 4 - 4 * Real.sqrt 3 * (x - 1)) / (x - 1) := by
        field_simp
        <;> ring
      rw [h10] at *
      apply div_nonneg
      -- Show the numerator is non-negative
      nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg ((x - 1) - 2 * Real.sqrt 3 / 3), sq_nonneg (3 * (x - 1) - 2 * Real.sqrt 3), sq_nonneg (x -1), sq_nonneg (Real.sqrt 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith) ]
      all_goals linarith
    linarith

  linarith [h4]