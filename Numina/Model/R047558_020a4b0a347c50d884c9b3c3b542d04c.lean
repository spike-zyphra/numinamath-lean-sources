import Mathlib

theorem inequalities_277297 (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i) :
    (x 0 + x 1 + x 2 + x 3 + x 4)^2 ≥
    4 * (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 + x 4 * x 0) := by
  have h1 : 0 < x 0 := hx 0
  have h2 : 0 < x 1 := hx 1
  have h3 : 0 < x 2 := hx 2
  have h4 : 0 < x 3 := hx 3
  have h5 : 0 < x 4 := hx 4
  have h6 : (x 0 + x 1 + x 2 + x 3 + x 4) ^ 2 - 4 * (x 0 * x 1 + x 1 * x 2 + x 2 * x 3 + x 3 * x 4 + x 4 * x 0) ≥ 0 := by
    nlinarith [sq_nonneg (x 0 - x 1 + x 2 - x 3 + x 4), 
          sq_nonneg (x 0 - x 2 + x 4 - x 1 + x 3), 
          sq_nonneg (x 0 - x 3 + x 1 - x 4 + x 2), 
          sq_nonneg (x 0 - x 4 + x 3 - x 1 + x 2), 
          sq_nonneg (x 1 - x 0 + x 3 - x 2 + x 4), 
          sq_nonneg (x 1 - x 2 + x 3 - x 0 + x 4), 
          sq_nonneg (x 2 - x 3 + x 4 - x 0 + x 1), 
          sq_nonneg (x 3 - x 4 + x 0 - x 1 + x 2), 
          mul_pos h1 h2, mul_pos h2 h3, mul_pos h3 h4, mul_pos h4 h5, mul_pos h5 h1
        ]
  linarith