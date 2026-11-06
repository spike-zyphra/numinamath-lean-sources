import Mathlib.Tactic

theorem inequalities_125650 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a + b) * (a + c) ≥ 2 * Real.sqrt (a * b * c * (a + b + c)) := by
  have h8 : (a + b) * (a + c) = a * (a + b + c) + b * c := by 
    ring
  have h9 : (a + b) * (a + c) ≥ 2 * Real.sqrt (a * (a + b + c) * (b * c)) := by
    have h5 : a * (a + b + c) ≥ 0 := by positivity
    have h6 : b * c ≥ 0 := by positivity
    have h7 : a * (a + b + c) + b * c ≥ 2 * Real.sqrt (a * (a + b + c) * (b * c)) := by
      have h10 : a * (a + b + c) * (b * c) ≥ 0 := by positivity
      have h11 : (Real.sqrt (a * (a + b + c) * (b * c))) ^ 2 = a * (a + b + c) * (b * c) := Real.sq_sqrt (by positivity)
      nlinarith [sq_nonneg (a * (a + b + c) - b * c), sq_nonneg (Real.sqrt (a * (a + b + c) * (b * c)) - ((a * (a + b + c)) + (b * c)) / 2), 
          h11, 
          sq_nonneg (Real.sqrt (a * (a + b + c) * (b * c)) + Real.sqrt (a * (a + b + c) * (b * c))), 
          Real.sqrt_nonneg (a * (a + b + c) * (b * c)), 
          sq_nonneg (a * (a + b + c) - b * c), 
          mul_nonneg (Real.sqrt_nonneg (a * (a + b + c) * (b * c))) (Real.sqrt_nonneg (a * (a + b + c) * (b * c)))
        ]
    linarith [h8]
  have h20 : Real.sqrt (a * (a + b + c) * (b * c)) = Real.sqrt (a * b * c * (a + b + c)) := by
    ring_nf
  rw [h20] at h9
  linarith [h8, h9]