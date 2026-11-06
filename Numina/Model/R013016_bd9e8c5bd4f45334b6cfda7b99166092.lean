import Mathlib

theorem algebra_188355 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^3 + Real.sqrt x = y^3 + Real.sqrt y ↔ (x = y) := by
  constructor
  · -- Assume x^3 + Real.sqrt x = y^3 + Real.sqrt y, prove x = y
    intro h
    have h1 : Real.sqrt x ≥ 0 := by positivity
    have h2 : Real.sqrt y ≥ 0 := by positivity
    by_cases h3 : x < y
    · -- Assume x < y
      have h4 : Real.sqrt x < Real.sqrt y := by
        apply Real.sqrt_lt_sqrt
        linarith
        linarith
      have h5 : x^3 < y^3 := by
        have h4 : x < y := h3
        have h6 : 0 < y - x := by linarith
        have h7 : y^3 - x^3 = (y - x) * (y^2 + y * x + x^2) := by
          ring_nf
        have h8 : 0 < y - x := by linarith
        have h9 : 0 < y^2 + y * x + x^2 := by
          nlinarith [sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (y), sq_nonneg (x), h6]
        have h10 : (y - x) * (y^2 + y * x + x^2) > 0 := by
          apply mul_pos
          · linarith
          all_goals nlinarith
        have h11 : y^3 - x^3 > 0 := by
          linarith
        nlinarith
      nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith),
        Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith),
        Real.sqrt_nonneg x, Real.sqrt_nonneg y,
        sq_nonneg (Real.sqrt x - Real.sqrt y),
        sq_nonneg (x - y), sq_pos_of_pos (show 0 < 2 by norm_num)
      ]
    · -- Assume x ≥ y
      by_cases h4 : x > y
      · -- Assume x > y
        have h4' : x > y := h4
        have h8 : Real.sqrt x > Real.sqrt y := by
          apply Real.sqrt_lt_sqrt
          linarith
          linarith
        have h9 : x^3 > y^3 := by
          have h4' : x > y := h4
          have h6 : 0 < x - y := by linarith
          have h7 : x^3 - y^3 = (x - y) * (x^2 + x * y + y^2) := by
            ring_nf
          have h10 : 0 < x - y := by linarith
          have h11 : 0 < x^2 + x * y + y^2 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x), sq_nonneg (y), h6]
          have h12 : (x - y) * (x^2 + x * y + y^2) > 0 := by
            apply mul_pos
            · linarith
            all_goals nlinarith
          have h13 : x^3 - y^3 > 0 := by
            linarith
          nlinarith
        nlinarith [Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith),
          Real.sq_sqrt (show 0 ≤ (y : ℝ) by linarith),
          Real.sqrt_nonneg x, Real.sqrt_nonneg y,
          sq_nonneg (Real.sqrt x - Real.sqrt y),
          sq_nonneg (x - y), sq_pos_of_pos (show 0 < 2 by norm_num)
        ]
      · -- Assume x = y
        have h5 : x = y := by linarith
        exact h5
  · -- Assume x = y
    intro h
    rw [h]