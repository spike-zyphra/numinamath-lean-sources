import Mathlib
set_option maxHeartbeats 1000000
open Real

theorem inequalities_104375 (x y z : ℝ) (h : x^4 + y^4 + z^4 ≤ 48) :
    x^2 + y^2 + z^2 ≤ 12 ∧
    1 ≤ 1 / sqrt (1 + x^2 + y^2) + 1 / sqrt (1 + y^2 + z^2) +
        1 / sqrt (1 + z^2 + x^2) := by
  have h1 : x^2 + y^2 + z^2 ≤ 12 := by
    nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4),
          sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
          sq_nonneg (x^4 + y^4 + z^4 - 48)]
  have h2 : 1 ≤ 1 / sqrt (1 + x^2 + y^2) + 1 / sqrt (1 + y^2 + z^2) +
      1 / sqrt (1 + z^2 + x^2) := by
    have h3 : sqrt (1 + x^2 + y^2) > 0 := by
      apply sqrt_pos.2
      nlinarith [sq_nonneg x, sq_nonneg y]
    have h4 : sqrt (1 + y^2 + z^2) > 0 := by
      apply sqrt_pos.2
      nlinarith [sq_nonneg y, sq_nonneg z]
    have h5 : sqrt (1 + z^2 + x^2) > 0 := by
      apply sqrt_pos.2
      nlinarith [sq_nonneg z, sq_nonneg x]
    have hx1 : 1 / sqrt (1 + x^2 + y^2) + 1 / sqrt (1 + y^2 + z^2) + 1 / sqrt (1 + z^2 + x^2) ≥ 1 := by
      have h7 : sqrt (1 + x^2 + y^2) * sqrt (1 + y^2 + z^2) * sqrt (1 + z^2 + x^2) > 0 := by positivity
      have hx2 : (1 / sqrt (1 + x^2 + y^2) + 1 / sqrt (1 + y^2 + z^2) + 1 / sqrt (1 + z^2 + x^2) ) - 1 ≥ 0 := by
        have eq1 : (1 / sqrt (1 + x^2 + y^2) + 1 / sqrt (1 + y^2 + z^2) + 1 / sqrt (1 + z^2 + x^2) ) - 1 =
            (sqrt (1 + y^2 + z^2) * sqrt (1 + z^2 + x^2) + sqrt (1 + x^2 + y^2) * sqrt (1 + z^2 + x^2) + sqrt (1 + x^2 + y^2) * sqrt (1 + y^2 + z^2) - sqrt (1 + x^2 + y^2) * sqrt (1 + y^2 + z^2) * sqrt (1 + z^2 + x^2)) / (sqrt (1 + x^2 + y^2) * sqrt (1 + y^2 + z^2) * sqrt (1 + z^2 + x^2)) := by
          field_simp 
          <;> ring 
        rw [eq1] at *
        apply div_nonneg 
        have h7 : x^4 + y^4 + z^4 ≤ 48 := h 
        nlinarith [Real.sqrt_nonneg (1 + x^2 + y^2), Real.sqrt_nonneg (1 + y^2 + z^2), Real.sqrt_nonneg (1 + z^2 + x^2), 
            sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4), 
            Real.sq_sqrt (show 0 ≤ (1 + x^2 + y^2 : ℝ) by positivity), 
            Real.sq_sqrt (show 0 ≤ (1 + y^2 + z^2 : ℝ) by positivity), 
            Real.sq_sqrt (show 0 ≤ (1 + z^2 + x^2 : ℝ) by positivity), 
            mul_nonneg (Real.sqrt_nonneg (1 + x^2 + y^2)) (Real.sqrt_nonneg (1 + y^2 + z^2)), 
            mul_nonneg (Real.sqrt_nonneg (1 + y^2 + z^2)) (Real.sqrt_nonneg (1 + z^2 + x^2)), 
            mul_nonneg (Real.sqrt_nonneg (1 + z^2 + x^2)) (Real.sqrt_nonneg (1 + x^2 + y^2)), 
            sq_nonneg (sqrt (1 + x^2 + y^2) - 3), sq_nonneg (sqrt (1 + y^2 + z^2) - 3), sq_nonneg (sqrt (1 + z^2 + x^2) - 3)
        ]
        all_goals positivity 
      linarith
    linarith 
  exact ⟨h1, h2⟩