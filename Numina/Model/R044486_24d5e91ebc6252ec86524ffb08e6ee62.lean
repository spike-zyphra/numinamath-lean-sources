import Mathlib

theorem algebra_318449 (x y : ℝ) (a : ℝ) (hx : x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4)) (hy : y ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4))
    (h1 : x^3 + Real.sin x - 2 * a = 0) (h2 : 4 * y^3 + (1 / 2) * Real.sin (2 * y) + a = 0) :
    Real.cos (x + 2 * y) = 1 := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  have h3 : x^3 + Real.sin x = 2 * a := by linarith
  have h5 : 8 * y^3 + Real.sin (2 * y) + (x^3 + Real.sin x) = 0 := by
    have h6 : 2 * a = x^3 + Real.sin x := by linarith
    have h7 : 8 * y^3 + Real.sin (2 * y) + (x^3 + Real.sin x) = 0 := by
      have h8 : 8 * y^3 + Real.sin (2 * y) + (2 * a) = 0 := by
        have h9 : 4 * y^3 + (1 / 2) * Real.sin (2 * y) + a = 0 := h2
        have h10 : 8 * y^3 + Real.sin (2 * y) + (2 * a) = 2 * (4 * y^3 + (1 / 2) * Real.sin (2 * y) + a) := by ring
        rw [h9] at h10
        linarith
      linarith [h6, h8]
    linarith
  have eq1 : x ^ 3 + Real.sin x + ((2 * y) ^ 3 + Real.sin (2 * y)) = 0 := by
    have eq2 : 8 * y^3 + Real.sin (2 * y) + (x^3 + Real.sin x) = 0 := by
      linarith [h5]
    have eq3 : (2 * y) ^ 3 + Real.sin (2 * y) = 8 * y^3 + Real.sin (2 * y) := by
      ring_nf
    linarith [eq2, eq3]
  have h7 : x = -2 * y := by
    have h8 : x ^ 3 + Real.sin x = - ((2 * y) ^ 3 + Real.sin (2 * y)) := by
      linarith [eq1]
    have h9 : x ^ 3 + Real.sin x = ((-2 * y) ^ 3 + Real.sin (-2 * y)) := by
      have h10 : Real.sin (-2 * y) = - Real.sin (2 * y) := by 
        rw [show -2 * y = - (2 * y) by ring]
        rw [Real.sin_neg]
      have h11 : ((-2 * y) ^ 3 + Real.sin (-2 * y)) = - ((2 * y) ^ 3 + Real.sin (2 * y)) := by
        rw [h10]
        ring_nf
      linarith [h8, h11]
    have h14 : x = -2 * y := by
      have h15 : x ≤ -2 * y := by
        by_contra h
        push_neg at h
        have h16 : x ^ 3 + Real.sin x > (-2 * y) ^ 3 + Real.sin (-2 * y) := by
          have h17 : x > -2 * y := h
          have h18 : -Real.pi / 2 ≤ -2 * y := by
            nlinarith [Real.pi_pos, hy1, hy2]
          have h19 : -2 * y ≤ Real.pi / 2 := by
            nlinarith [Real.pi_pos, hy1, hy2]
          have h20 : x ≤ Real.pi / 2 := by
            nlinarith [Real.pi_pos, hx1, hx2]
          have h21 : Real.sin x > Real.sin (-2 * y) := by
            apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals
              nlinarith [Real.pi_pos, hx1, hx2, hy1, hy2, h17]
          have h22 : x ^ 3 > (-2 * y) ^ 3 := by
            have h23 : x > -2 * y := h
            have h24 : x ^ 2 + x * (-2 * y) + (-2 * y) ^ 2 > 0 := by
              nlinarith [sq_nonneg (x + (-2 * y)), sq_nonneg (x), sq_nonneg (-2 * y), sq_nonneg (x - (-2 * y)), sq_nonneg (x * (-2 * y)), Real.pi_pos]
            nlinarith [sq_nonneg (x + (-2 * y)), sq_nonneg (x * (-2 * y)), mul_pos (show (0 : ℝ) < 3 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
          nlinarith [h21, h22]
        linarith [h9, h16]
      have h16 : x ≥ -2 * y := by
        by_contra h
        push_neg at h
        have h17 : x < -2 * y := h
        have h18 : x ^ 3 + Real.sin x < (-2 * y) ^ 3 + Real.sin (-2 * y) := by
          have h17 : x < -2 * y := h
          have h18 : -Real.pi / 2 ≤ -2 * y := by
            nlinarith [Real.pi_pos, hy1, hy2]
          have h19 : -2 * y ≤ Real.pi / 2 := by
            nlinarith [Real.pi_pos, hy1, hy2]
          have h20 : x ≤ Real.pi / 2 := by
            nlinarith [Real.pi_pos, hx1, hx2]
          have h21 : Real.sin x < Real.sin (-2 * y) := by
            apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
            all_goals
              nlinarith [Real.pi_pos, hx1, hx2, hy1, hy2, h17]
          have h22 : x ^ 3 < (-2 * y) ^ 3 := by
            have h23 : x < -2 * y := h
            have h24 : x ^ 2 + x * (-2 * y) + (-2 * y) ^ 2 > 0 := by
              nlinarith [sq_nonneg (x + (-2 * y)), sq_nonneg (x), sq_nonneg (-2 * y), sq_nonneg (x - (-2 * y)), sq_nonneg (x * (-2 * y)), Real.pi_pos]
            nlinarith [sq_nonneg (x + (-2 * y)), sq_nonneg (x * (-2 * y)), mul_pos (show (0 : ℝ) < 3 by norm_num) (show (0 : ℝ) < 1 by norm_num)]
          nlinarith [h21, h22]
        linarith [h9, h18]
      linarith
    linarith
  have h17 : x + 2 * y = 0 := by
    linarith [h7]
  have h18 : Real.cos (x + 2 * y) = 1 := by
    rw [h17]
    norm_num
  exact h18