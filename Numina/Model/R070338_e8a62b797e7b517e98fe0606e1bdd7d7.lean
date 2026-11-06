import Mathlib

theorem algebra_198428 {p q r : ℝ} (f : ℝ → ℝ) (hf : f = fun x => p * x ^ 7 + q * x ^ 3 + r * x - 5)
    (h : f (-6) = 3) (z : ℝ) (hz : z = f 6) : z = -13 := by 
  have eq1 : f (-6) = p * (-6) ^ 7 + q * (-6) ^ 3 + r * (-6) - 5 := by 
    rw [hf]
  have eq2 : f 6 = p * 6 ^ 7 + q * 6 ^ 3 + r * 6 - 5 := by 
    rw [hf]
  rw [eq1] at h
  rw [eq2] at hz 
  have eq4 : p * 6 ^ 7 + q * 6 ^ 3 + r * 6 = -8 := by
    have eq5 : p * (-6) ^ 7 + q * (-6) ^ 3 + r * (-6) = 8 := by
      linarith 
    have eq6 : p * (-6) ^ 7 + q * (-6) ^ 3 + r * (-6) = - (p * 6 ^ 7 + q * 6 ^ 3 + r * 6) := by
      ring_nf 
    linarith [eq5, eq6]
  linarith [hz, eq4]