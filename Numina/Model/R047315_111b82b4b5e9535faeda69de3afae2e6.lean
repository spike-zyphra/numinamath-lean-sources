import Mathlib

theorem inequalities_129586 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x - Real.sqrt x ≤ y - 1 / 4 ∧ y - 1 / 4 ≤ x + Real.sqrt x) :
    y - Real.sqrt y ≤ x - 1 / 4 ∧ x - 1 / 4 ≤ y + Real.sqrt y := by 
  have h1 : x - Real.sqrt x ≤ y - 1 / 4 := h.1
  have h2 : y - 1 / 4 ≤ x + Real.sqrt x := h.2
  have h3 : 0 ≤ Real.sqrt x := by 
    apply Real.sqrt_nonneg
  have h4 : 0 ≤ Real.sqrt y := by 
    apply Real.sqrt_nonneg
  have h5 : 0 < x := hx
  have h6 : 0 < y := hy
  have h7 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h8 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  constructor
  · -- Prove the first part: y - sqrt y ≤ x - 1/4
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      Real.sq_sqrt (show 0 ≤ x by linarith), 
      Real.sq_sqrt (show 0 ≤ y by linarith), 
      sq_nonneg (Real.sqrt x - 1 / 2), sq_nonneg (Real.sqrt y - 1 / 2), 
      sq_nonneg (Real.sqrt x - Real.sqrt y), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      mul_pos hx hy, 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  · -- Prove the second part: x - 1/4 ≤ y + sqrt y
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      Real.sq_sqrt (show 0 ≤ x by linarith), 
      Real.sq_sqrt (show 0 ≤ y by linarith), 
      sq_nonneg (Real.sqrt x - 1 / 2), sq_nonneg (Real.sqrt y - 1 / 2), 
      sq_nonneg (Real.sqrt x - Real.sqrt y), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      mul_pos hx hy, 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]