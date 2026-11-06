import Mathlib

open Real

theorem inequalities_47738 (x y : ℝ) (h : x ≠ 0 ∨ y ≠ 0) :
    (x + y) / (x ^ 2 - x * y + y ^ 2) ≤ 2 * sqrt 2 / sqrt (x ^ 2 + y ^ 2) := by

  have h1 : x ^ 2 - x * y + y ^ 2 > 0 := by
    by_cases hx : x ≠ 0
    · -- Assume x ≠ 0
      nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y)]
    · -- Assume x = 0
      have : x = 0 := by
        simpa using hx
      have hy : y ≠ 0 := by
        tauto
      rw [this]
      nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (0 : ℝ), sq_nonneg (y), sq_nonneg (y)]
  
  have h2 : x ^ 2 + y ^ 2 > 0 := by
    by_cases hx : x ≠ 0
    · -- Assume x ≠ 0
      nlinarith [sq_pos_of_ne_zero hx, sq_nonneg (x - y), sq_nonneg (y), sq_nonneg (x + y)]
    · -- Assume x = 0
      have : x = 0 := by
        simpa using hx
      have hy : y ≠ 0 := by
        tauto
      rw [this]
      nlinarith [sq_pos_of_ne_zero hy, sq_nonneg (0 : ℝ), sq_nonneg (y), sq_nonneg (y)]
  
  have h3 : sqrt (x ^ 2 + y ^ 2) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith

  by_cases h4 : x + y ≥ 0
  · -- Assume (x + y) ≥ 0
    have h5 : (x + y) * sqrt (x ^ 2 + y ^ 2) ≤ 2 * sqrt 2 * (x^ 2 - x * y + y^ 2) := by
      have h6 : ((x + y) * sqrt (x ^ 2 + y ^ 2)) ^ 2 ≤ (2 * sqrt 2 * (x^ 2 - x * y + y^ 2)) ^ 2 := by
        have h7 : ((x + y) * sqrt (x ^ 2 + y ^ 2)) ^ 2 = (x + y) ^ 2 * (sqrt (x^ 2 + y ^ 2)) ^ 2 := by 
          ring_nf
        have h8 : (sqrt (x^ 2 + y ^ 2)) ^ 2 = x^ 2 + y ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith [h2]
        have h9 : ((x + y) * sqrt (x ^ 2 + y ^ 2)) ^ 2 = (x + y) ^ 2 * (x^ 2 + y ^ 2) := by
          rw [h7, h8]
        have h10 : (2 * sqrt 2 * (x^ 2 - x * y + y^ 2))^ 2 = 8 * ((x^ 2 - x * y + y^ 2) ^ 2) := by
          calc
            (2 * sqrt 2 * (x^ 2 - x * y + y^ 2))^ 2
                = (2 * sqrt 2) ^ 2 * ((x^ 2 - x * y + y^ 2) ^ 2) := by ring_nf
            _ = 4 * (sqrt 2)^2 * ((x^ 2 - x * y + y^ 2) ^ 2) := by ring_nf
            _ = 4 * 2 * ((x^ 2 - x * y + y^ 2) ^ 2) := by
              have h11 : (sqrt 2 : ℝ) ^ 2 = 2 := by norm_num [Real.sq_sqrt]
              rw [h11]
            _ = 8 * ((x^ 2 - x * y + y^ 2) ^ 2) := by ring_nf
        rw [h9, h10]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y),
                  sq_nonneg ((x^2 + y^2) - x * y), sq_nonneg (x^2 + y^2 - x * y),
                  sq_nonneg (7 * (x^2 + y^2) - 11 * (x * y)), sq_nonneg (x^2 + y^2 - 7 * (x * y)), sq_pos_of_pos h3, sq_pos_of_pos h1
        ]
      have h7 : 0 ≤ (x + y) * sqrt (x ^ 2 + y ^ 2) := by
        apply mul_nonneg
        linarith
        positivity
      have h8 : 0 ≤ 2 * sqrt 2 * (x^ 2 - x * y + y^ 2) := by
        positivity
      nlinarith
    have h14 : (x + y) / (x ^ 2 - x * y + y ^ 2) ≤ 2 * sqrt 2 / sqrt (x ^ 2 + y ^ 2) := by
      have h15 : sqrt (x ^ 2 + y ^ 2) > 0 := h3
      have h16 : x ^ 2 - x * y + y ^ 2 > 0 := h1
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h14
  · -- Assume (x + y) < 0
    push_neg at h4
    have h11 : (x + y) * sqrt (x ^ 2 + y ^ 2) < (2 * sqrt 2 * (x ^ 2 - x * y + y ^ 2) ) := by
      have h17 : (x + y) * sqrt (x ^ 2 + y ^ 2) < (0 : ℝ) := by
        have h18 : sqrt (x ^ 2 + y ^ 2) > 0 := h3
        have h19 : x + y < 0 := h4
        nlinarith
      have h18 : 0 < 2 * sqrt 2 * (x ^ 2 - x * y + y ^ 2) := by
        positivity
      nlinarith
    have h14 : (x + y) / (x ^ 2 - x * y + y ^ 2) ≤ 2 * sqrt 2 / sqrt (x ^ 2 + y ^ 2) := by
      have h15 : sqrt (x ^ 2 + y ^ 2) > 0 := h3
      have h16 : x ^ 2 - x * y + y ^ 2 > 0 := h1
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      nlinarith
    exact h14