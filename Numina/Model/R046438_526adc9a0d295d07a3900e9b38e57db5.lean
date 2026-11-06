import Mathlib

theorem algebra_231903 (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (h : a * Real.sqrt (1 - b^2) + b * Real.sqrt (1 - a^2) = 1) :
    a^2 + b^2 = 1 := by
  have ha1 : 0 ≤ a := ha.1
  have ha2 : a ≤ 1 := ha.2
  have hb1 : 0 ≤ b := hb.1
  have hb2 : b ≤ 1 := hb.2
  have h1 : 0 ≤ (1 - b ^ 2) := by
    nlinarith [hb1, hb2]
  have h2 : 0 ≤ (1 - a ^ 2) := by
    nlinarith [ha1, ha2]
  have h3 : Real.sqrt (1 - b ^ 2) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h4 : Real.sqrt (1 - a ^ 2) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h7 : (Real.sqrt (1 - b ^ 2)) ^ 2 = 1 - b ^ 2 := Real.sq_sqrt (by nlinarith)
  have h8 : (Real.sqrt (1 - a ^ 2)) ^ 2 = 1 - a ^ 2 := Real.sq_sqrt (by nlinarith)
  have h9 : a * Real.sqrt (1 - b^2) + b * Real.sqrt (1 - a^2) = 1 := h
  have h10 : (a * Real.sqrt (1 - b^2) + b * Real.sqrt (1 - a^2)) ^ 2 = 1 := by
    rw [h9]
    norm_num
  have h11 : a^2 * (Real.sqrt (1 - b ^ 2)) ^ 2 + b^2 * (Real.sqrt (1 - a ^ 2)) ^ 2 + 2 * (a * Real.sqrt (1 - b ^ 2) * (b * Real.sqrt (1 - a ^ 2))) = 1 := by
    nlinarith [h10]
  rw [h7] at h11
  rw [h8] at h11
  nlinarith [Real.sqrt_nonneg (1 - b ^ 2), Real.sqrt_nonneg (1 - a ^ 2), 
          mul_nonneg (Real.sqrt_nonneg (1 - b ^ 2)) (Real.sqrt_nonneg (1 - a ^ 2)), 
          sq_nonneg (a - Real.sqrt (1 - b ^ 2)), 
          sq_nonneg (b - Real.sqrt (1 - a ^ 2)), 
          mul_nonneg ha1 hb1, 
          mul_nonneg (show 0 ≤ 1 - b ^ 2 by nlinarith) (show 0 ≤ 1 - a ^ 2 by nlinarith), 
          sq_nonneg (a ^ 2 + b ^ 2 - 1) ]