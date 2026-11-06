import Mathlib

open Real

theorem algebra_141676 {x : ℝ} (hx : -1 ≤ x ∧ x < 1) :
    ((1 - x) * sqrt ((1 + x) / (1 - x)) + 1 - x) * (sqrt ((1 + x) / (1 - x)) - 1) = 2 * x := by
  have h1 : -1 ≤ x := hx.1
  have h2 : x < 1 := hx.2
  have h3 : 0 < 1 - x := by linarith
  have h4 : 0 ≤ 1 + x := by linarith
  have h5 : ((1 + x) / (1 - x)) ≥ 0 := by
    apply div_nonneg
    linarith
    linarith
  have h6 : (sqrt ((1 + x) / (1 - x))) ^ 2 = (1 + x) / (1 - x) := Real.sq_sqrt (show (1 + x) / (1 - x) ≥ 0 by linarith)
  have h7 : (1 - x) * (sqrt ((1 + x) / (1 - x)) ^ 2) = 1 + x := by
    have h8 : (sqrt ((1 + x) / (1 - x))) ^ 2 = (1 + x) / (1 - x) := h6
    rw [h8]
    field_simp [(show 1 - x ≠ 0 by linarith)]
    all_goals linarith
  calc
    ((1 - x) * sqrt ((1 + x) / (1 - x)) + 1 - x) * (sqrt ((1 + x) / (1 - x)) - 1)
      = ((1 - x) * (sqrt ((1 + x) / (1 - x)) ) ^ 2 - (1 - x)) := by 
        ring_nf
    _ = (1 - x) * (sqrt ((1 + x) / (1 - x)) ^ 2) - (1 - x) := by ring
    _ = (1 + x) - (1 - x) := by 
      rw [show (1 - x) * (sqrt ((1 + x) / (1 - x)) ^ 2) = 1 + x by linarith [h7]]
    _ = 2 * x := by 
      ring