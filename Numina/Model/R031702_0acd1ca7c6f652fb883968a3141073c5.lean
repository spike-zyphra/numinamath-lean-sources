import Mathlib

open Real

theorem inequalities_215741 (x : ℝ) (hx : 0 < x) :
    sqrt (2 * x * sqrt ((2 * x + 1) * sqrt ((2 * x + 2) * sqrt (2 * x + 3)))) <
    (15 * x + 6) / 8 := by
  have h1 : 0 < 2 * x := by nlinarith
  have h2 : 0 < (2 * x + 1 : ℝ) := by nlinarith
  have h3 : 0 < (2 * x + 2 : ℝ) := by nlinarith
  have h4 : 0 < (2 * x + 3 : ℝ) := by nlinarith
  have h5 : Real.sqrt (2 * x + 3) ≥ 0 := Real.sqrt_nonneg (2 * x + 3)
  have h6 : Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) ≥ 0 := by positivity
  have h7 : Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))) ≥ 0 := by positivity
  have h8 : Real.sqrt (2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)))) ≥ 0 := by positivity

  have h13 : 2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))) < (225 * x ^ 2 + 180 * x + 36) / 64 := by
    have h5 : Real.sqrt (2 * x + 3) ≥ 0 := Real.sqrt_nonneg (2 * x + 3)
    have h6 : Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) ≥ 0 := by positivity
    have h7 : Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))) ≥ 0 := by positivity

    have h30 : Real.sqrt (2 * x + 3) ^ 2 = 2 * x + 3 := Real.sq_sqrt (by nlinarith)
    have h31 : Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) ^ 2 = (2 * x + 2) * Real.sqrt (2 * x + 3) := Real.sq_sqrt (by positivity)
    have h32 : Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))) ^ 2 = (2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) := Real.sq_sqrt (by positivity)

    nlinarith [sq_nonneg (Real.sqrt (2 * x + 3) - ( (2 * x + 3) ) / 2 ), 
          sq_nonneg (Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) - ( (2 * x + 2) * Real.sqrt (2 * x + 3) ) / 2 ), 
          sq_nonneg (Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))) - ( (2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) ) / 2 ), 
          Real.sqrt_nonneg (2 * x + 3), 
          Real.sqrt_nonneg ((2 * x + 2) * Real.sqrt (2 * x + 3)), 
          Real.sqrt_nonneg ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 3) by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 2) * Real.sqrt (2 * x + 3) by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)) by positivity), 
          mul_nonneg (Real.sqrt_nonneg (2 * x + 3)) (Real.sqrt_nonneg ((2 * x + 2) * Real.sqrt (2 * x + 3))), 
          mul_nonneg (Real.sqrt_nonneg ((2 * x + 2) * Real.sqrt (2 * x + 3))) (Real.sqrt_nonneg ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)))),
          mul_pos hx (show 0 < 2 * x by linarith), 
          mul_pos (show 0 < 2 * x by linarith) (show 0 < 2 * x + 1 by linarith), 
          mul_pos (show 0 < 2 * x + 1 by linarith) (show 0 < 2 * x + 2 by linarith), 
          mul_pos (show 0 < 2 * x + 2 by linarith) (show 0 < 2 * x + 3 by linarith)]

  have h9 : Real.sqrt (2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)))) < (15 * x + 6) / 8 := by

    have h11 : (Real.sqrt (2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))))) ^ 2 = 2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))) := by
      rw [Real.sq_sqrt]
      positivity

    have h12 : ((15 * x + 6) / 8) ^ 2 = (225 * x ^ 2 + 180 * x + 36) / 64 := by
      ring_nf

    have h14 : (Real.sqrt (2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))))) ^ 2 < ((15 * x + 6) / 8) ^ 2 := by
      nlinarith [h13, h11, h12]

    have h15 : Real.sqrt (2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3)))) ≥ 0 := by positivity
    have h16 : (15 * x + 6) / 8 ≥ 0 := by nlinarith

    nlinarith [Real.sqrt_nonneg (2 * x * Real.sqrt ((2 * x + 1) * Real.sqrt ((2 * x + 2) * Real.sqrt (2 * x + 3))))]

  exact h9