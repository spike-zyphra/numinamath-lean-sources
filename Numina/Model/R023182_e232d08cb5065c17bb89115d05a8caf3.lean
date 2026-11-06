import Mathlib

theorem inequalities_198008 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y = 1) :
    (1 / x ^ 2 - 1) * (1 / y ^ 2 - 1) ≥ 9 := by
  have h1 : y = 1 - x := by
    linarith
  rw [h1]
  -- We need to prove that (1 / x ^ 2 - 1) * (1 / (1 - x) ^ 2 - 1) ≥ 9
  -- Now, note that x and 1 - x are both positive.
  have h2 : 0 < 1 - x := by
    nlinarith
  -- Compute the product moving 9 to left side.
  -- $\left(\frac{1}{x^2}-1\right) \cdot \left(\frac{1}{(1-x)^2}-1\right) - 9 \geq 0$
  have h4 : (1 / x ^ 2 - 1) * (1 / (1 - x) ^ 2 - 1) - 9 ≥ 0 := by
    have pos1 : 0 < x ^ 2 := by positivity
    have pos2 : 0 < (1 - x) ^ 2 := by positivity
    have h5 : x * (1 - x) > 0 := mul_pos hx h2
    -- Express the inequality as a single fraction.
    have h6 : (1 / x ^ 2 - 1) * (1 / (1 - x) ^ 2 - 1) - 9 =
        ( (1 - x^2) * (1 - (1 - x) ^ 2) - 9 * x^2 * (1 - x) ^ 2 ) / (x^2 * (1 - x) ^ 2) := by
      field_simp
      <;> ring
    rw [h6]
    -- Prove the numerator is ≥ 0 and denominator is > 0.
    have h7 : ( (1 - x^2) * (1 - (1 - x) ^ 2) - 9 * x^2 * (1 - x) ^ 2 ) ≥ 0 := by
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x - 1 / 3), sq_nonneg (x - 2 / 3), 
          sq_nonneg (x * (x - 1 / 2)), sq_nonneg ((1 - x) * (x - 1 / 2)), 
          mul_pos hx h2, mul_pos hx h2, mul_pos h2 h2
        ]
    have h8 : ( (1 - x^2) * (1 - (1 - x) ^ 2) - 9 * x^2 * (1 - x) ^ 2 ) / (x^2 * (1 - x) ^ 2) ≥ 0 := by
      apply div_nonneg
      linarith
      all_goals
        positivity
    linarith [h7, h8]
  -- The inequality is proven.
  linarith [h4]