import Mathlib

open Real

theorem inequalities_606254 (x y : ℝ) (h : x^2 + y^2 ≠ 0) :
  (x + y) / (x ^ 2 - x * y + y ^ 2) ≤ 2 * sqrt 2 / sqrt (x ^ 2 + y ^ 2) := by
  have h1 : x^2 - x * y + y^2 > 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_pos_of_ne_zero (show x^2 + y^2 ≠ 0 by assumption)]
  have h2 : sqrt (x^2 + y^2) > 0 := by
    apply Real.sqrt_pos.mpr
    have h3 : x ^ 2 + y ^ 2 > 0 := by
      by_contra h3
      push_neg at h3
      have h4 : x ^ 2 + y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
      contradiction
    linarith

  have h3 : (x + y) * sqrt (x^2 + y^2) ≤ 2 * Real.sqrt 2 * (x^2 - x * y + y^2) := by
    by_cases h4 : (x + y) ≥ 0
    · -- If x + y ≥ 0, we can square both sides.
      have h5 : ((x + y) * sqrt (x^2 + y^2)) ^ 2 ≤ (2 * Real.sqrt 2 * (x^2 - x * y + y^2)) ^ 2 := by
        have h6 : ((x + y) * sqrt (x^2 + y^2)) ^ 2 = (x + y) ^ 2 * (x^2 + y^2) := by
          calc
            ((x + y) * sqrt (x^2 + y^2)) ^ 2 = (x + y) ^ 2 * (sqrt (x^2 + y^2) ^ 2) := by ring
            _ = (x + y) ^ 2 * (x^2 + y^2) := by rw [Real.sq_sqrt]; positivity
        have h7 : (2 * Real.sqrt 2 * (x^2 - x * y + y^2)) ^ 2 = 8 * (x^2 - x * y + y^2) ^ 2 := by
          calc
            (2 * Real.sqrt 2 * (x^2 - x * y + y^2)) ^ 2 = 4 * (Real.sqrt 2) ^ 2 * (x^2 - x * y + y^2) ^ 2 := by ring
            _ = 4 * 2 * (x^2 - x * y + y^2) ^ 2 := by
              have h8 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
              rw [h8]
            _ = 8 * (x^2 - x * y + y^2) ^ 2 := by ring
        rw [h6, h7]
        have h8 : (x + y) ^ 2 * (x ^ 2 + y ^ 2) ≤ 8 * (x^2 - x * y + y^2) ^ 2 := by
          nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (x - y),
            sq_nonneg (x ^ 2 + y ^ 2 - 2 * (x * y)), sq_nonneg (x ^ 2 + y ^ 2 - 4 * (x + y) ^ 2),
            sq_nonneg ((x - y) * (x + y)), sq_nonneg (x^2 - 2 * y^2), sq_nonneg (2 * x^2 - y^2)
          ]
        linarith
      have h9 : (x + y) * sqrt (x^2 + y^2) ≤ 2 * Real.sqrt 2 * (x^2 - x * y + y^2) := by
        nlinarith [Real.sqrt_nonneg 2, show 0 ≤ (2 * Real.sqrt 2 * (x^2 - x * y + y^2) : ℝ) by positivity, show (0 : ℝ) ≤ (x + y) * sqrt (x^2 + y^2) by
          apply mul_nonneg
          · linarith [h4]
          · positivity
        ]
      linarith
    · -- x + y < 0
      have h10 : (x + y) * sqrt (x^2 + y^2) ≤ 2 * Real.sqrt 2 * (x^2 - x * y + y^2) := by
        have h11 : (x + y) < 0 := by linarith
        have h12 : (x + y) * sqrt (x^2 + y^2) ≤ 0 := by
          have h13 : sqrt (x^2 + y^2) ≥ 0 := Real.sqrt_nonneg (x^2 + y^2)
          nlinarith
        have h14 : 2 * Real.sqrt 2 * (x^2 - x * y + y^2) > 0 := by
          positivity
        nlinarith
      linarith

  have h4 : (x + y) / (x ^ 2 - x * y + y ^ 2) ≤ 2 * Real.sqrt 2 / sqrt (x ^ 2 + y^2) := by
    have h5 : (x + y) * sqrt (x^2 + y^2) ≤ 2 * Real.sqrt 2 * (x^2 - x * y + y^2) := h3
    have h6 : x^2 - x * y + y^2 > 0 := h1
    have h7 : sqrt (x^2 + y^2) > 0 := h2
    have h8 : (x + y) / (x ^ 2 - x * y + y ^ 2) - 2 * Real.sqrt 2 / sqrt (x ^ 2 + y^2) ≤ 0 := by
      have h9 : (x + y) / (x ^ 2 - x * y + y ^ 2) - 2 * Real.sqrt 2 / sqrt (x ^ 2 + y^2) =
          ((x + y) * sqrt (x^2 + y^2) - 2 * Real.sqrt 2 * (x^2 - x * y + y^2)) / ((x^2 - x * y + y^2) * sqrt (x^2 + y^2)) := by
        field_simp
        <;> ring
      rw [h9]
      have h10 : (x + y) * sqrt (x^2 + y^2) - 2 * Real.sqrt 2 * (x^2 - x * y + y^2) ≤ 0 := by
        linarith
      have h11 : (x^2 - x * y + y^2) * sqrt (x^2 + y^2) > 0 := by
        positivity
      apply div_nonpos_of_nonpos_of_nonneg h10 (by positivity)
    linarith
  exact h4