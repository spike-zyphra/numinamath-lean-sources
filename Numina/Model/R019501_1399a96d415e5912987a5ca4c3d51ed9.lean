import Mathlib

theorem inequalities_249179 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 + y^2 ≤ 1) :
    |x^2 + 2 * x * y - y^2| ≤ Real.sqrt 2 := by
  have h1 : (x^2 + 2 * x * y - y^2) ^ 2 ≤ 2 := by
    have h2 : (x^2 + 2 * x * y - y^2) ^ 2 ≤ 2 * ((x^2 - y^2) ^ 2 + (2 * x * y) ^ 2) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2 - 2 * x * y), sq_nonneg (x ^ 2 - y ^ 2 + 2 * x * y), 
        sq_nonneg (x * y), sq_nonneg (x^2 - y^2), sq_nonneg (2 * x * y), 
        mul_pos hx hy, mul_pos hx hx, mul_pos hy hy]
    have h3 : (x ^ 2 - y ^ 2) ^ 2 + (2 * x * y) ^ 2 = (x^2 + y^2) ^ 2 := by 
      ring
    have h4 : (x^2 + 2 * x * y - y^2) ^ 2 ≤ 2 * (x^2 + y^2) ^ 2 := by
      linarith [h2, h3]
    have h5 : 2 * (x^2 + y^2) ^ 2 ≤ 2 := by 
      nlinarith [h, sq_nonneg (x^2 + y^2), mul_pos hx hy]
    linarith [h4, h5]
  have h2 : |x^2 + 2 * x * y - y^2| ≤ Real.sqrt 2 := by 
    apply abs_le.mpr 
    constructor
    · -- Show that $x^2 + 2 * x * y - y^2 \geq -\sqrt{2}$
      have h7 : (x^2 + 2 * x * y - y^2) ≥ -Real.sqrt 2 := by 
        have h8 : (x^2 + 2 * x * y - y^2) ^ 2 ≤ 2 := h1 
        have h9 : -Real.sqrt 2 ≤ (x^2 + 2 * x * y - y^2) := by 
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        linarith 
      linarith 
    · -- Show that $x^2 + 2 * x * y - y^2 \leq \sqrt{2}$
      have h10 : (x^2 + 2 * x * y - y^2) ≤ Real.sqrt 2 := by 
        have h11 : (x^2 + 2 * x * y - y^2) ^ 2 ≤ 2 := h1 
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      linarith 
  exact h2