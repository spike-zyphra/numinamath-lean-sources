import Mathlib

theorem algebra_311706 {a : ℝ} (ha : a ≤ 24) (h : 0 ≤ 24 - a) (h' : 0 ≤ 8 - a)
    (h'' : Real.sqrt (24 - a) - Real.sqrt (8 - a) = 2) :
    Real.sqrt (24 - a) + Real.sqrt (8 - a) = 8 := by
  have h1 : Real.sqrt (24 - a) - Real.sqrt (8 - a) = 2 := h''
  have h2 : Real.sqrt (24 - a) ^ 2 = 24 - a := by
    rw [Real.sq_sqrt]
    linarith
  have h3 : Real.sqrt (8 - a) ^ 2 = 8 - a := by
    rw [Real.sq_sqrt]
    linarith
  have h4 : Real.sqrt (24 - a) ^ 2 - Real.sqrt (8 - a) ^ 2 = 16 := by
    rw [h2, h3]
    linarith
  have h6 : Real.sqrt (24 - a) ^ 2 - Real.sqrt (8 - a) ^ 2 = 
    (Real.sqrt (24 - a) - Real.sqrt (8 - a)) * (Real.sqrt (24 - a) + Real.sqrt (8 - a)) := by
    ring
  rw [h1] at h6
  nlinarith [Real.sqrt_nonneg (24 - a), Real.sqrt_nonneg (8 - a), h, h']