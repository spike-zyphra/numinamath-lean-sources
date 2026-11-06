import Mathlib

open Real
open scoped BigOperators

theorem inequalities_157231 {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ)
  (hf : f = λ x => (a - x)^6 - 3 * a * (a - x)^5 + (5 / 2) * a^2 * (a - x)^4 - (1 / 2) * a^4 * (a - x)^2)
  (x : ℝ) (hx : 0 < x ∧ x < a) : f x < 0 := by
  rw [hf]
  have h1 : 0 < x := hx.1
  have h2 : x < a := hx.2
  have h3 : 0 < a - x := by linarith
  have h4 : 0 < a := ha
  simp
  have h5 : (a - x) ^ 6 - 3 * a * (a - x) ^ 5 + (5 / 2) * a ^ 2 * (a - x) ^ 4 - (1 / 2) * a ^ 4 * (a - x) ^ 2 < 0 := by
    have h5 : 0 < a - x := h3
    have h6 : 0 < x := h1
    have h7 : 0 < a := h4
    have h8 : (a - x) * (a - x) > 0 := by nlinarith
    have h9 : x * (a - x) > 0 := by nlinarith
    nlinarith [ sq_nonneg ((a - x) ^ 2 - a * (a - x)), sq_nonneg ((a - x) - x), sq_nonneg ((a - x) ^ 2 - a * x), sq_nonneg (x^2 - (a - x) ^ 2), 
              sq_nonneg ((a - x) ^ 3 - a * (a - x) ^ 2), sq_nonneg (x^2 - a * x), sq_nonneg (a^2 - x^2), sq_nonneg ((a - x) * x), 
              mul_pos (show 0 < a - x by linarith) (show 0 < a by linarith), 
              mul_pos (show 0 < a - x by linarith) (show 0 < x by linarith), 
              mul_pos (show 0 < a - x by linarith) (show 0 < a^2 by positivity), 
              mul_pos (show 0 < a by linarith) (show 0 < a - x by linarith), 
              sq_nonneg (x - (a - x)), sq_nonneg ((a - x) ^ 2 - a^2 / 4), sq_nonneg (x - a / 2), sq_nonneg ((a - x) - a / 2), 
              pow_pos (show (0 : ℝ) < a - x by linarith) 3, 
              pow_pos (show (0 : ℝ) < a - x by linarith) 4, 
              pow_pos (show (0 : ℝ) < x by linarith) 3, 
              pow_pos (show (0 : ℝ) < x by linarith) 4 
            ]
  linarith