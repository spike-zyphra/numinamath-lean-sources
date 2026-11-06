import Mathlib



theorem algebra_607360 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) + (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) ≥ 5 := by
        -- First prove basic inequality facts
        have h1 : x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
        -- Derive that sum of squares ≥ 1
        have h2 : x ^ 2 + y ^ 2 + z ^ 2 ≥ 1 := by
            nlinarith [h, h1]

        -- For positive denominators
        have hx2 : x ^ 2 + 1 > 0 := by
            nlinarith
        have hy2 : y ^ 2 + 1 > 0 := by
            nlinarith
        have hz2 : z ^ 2 + 1 > 0 := by
            nlinarith

        -- Main proof by showing expression ≥ 0
        suffices 2 * (x ^ 2 + y ^ 2 + z ^ 2) + (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) - 5 ≥ 0 by linarith
        -- For positive denominator
        have pos2 : (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) > 0 := by positivity
        -- Key algebraic equivalence
        have eq6 : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) - 5 =
            ( 2 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) 
              + (4 / 3) * ( (y ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (y ^ 2 + 1) ) 
              - 5 * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ) / ((x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1)) := by
            field_simp
            ring
        have h3 : 2 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) 
            + (4 / 3) * ( (y ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (y ^ 2 + 1) ) 
            - 5 * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 0 := by
            nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                        sq_nonneg (x * y - 1 / 3), sq_nonneg (y * z - 1 / 3), sq_nonneg (z * x - 1 / 3),
                        sq_nonneg (x ^ 2 - 1 / 3), sq_nonneg (y ^ 2 - 1 / 3), sq_nonneg (z ^ 2 - 1 / 3),
                        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx
                      ]
        rw [eq6]
        apply div_nonneg
        linarith [h3]
        all_goals positivity