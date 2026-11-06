import Mathlib

theorem algebra_3358 {a b c : ℝ} (h : ∀ x y, (a*x+b*y+c)^2 = 54*x^2 + 24*y^2 + 72*x*y + 36*x + 24*y + 6) :
    Real.sqrt (a*b) = 6 := by
  have eq1 := h 0 0
  have eq2 := h 1 0
  have eq3 := h 0 1
  have eq4 := h 1 1
  have eq5 := h (-1) 0
  have eq6 := h 0 (-1)
  have hc1 : c^2 = 6 := by
    nlinarith
  have ha1 : (a + c)^2 = 96 := by
    nlinarith
  have hb1 : (b + c)^2 = 54 := by
    nlinarith
  have ha2 : (-a + c)^2 = 24 := by
    nlinarith
  have hb2 : (-b + c)^2 = 6 := by
    nlinarith
  have h7 : a * b = 36 := by
    nlinarith [sq_nonneg (a - 3 * Real.sqrt 6), sq_nonneg (a + 3 * Real.sqrt 6), sq_nonneg (b - 2 * Real.sqrt 6), sq_nonneg (b + 2 * Real.sqrt 6), Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
  have h8 : Real.sqrt (a * b) = Real.sqrt 36 := by
    rw [h7]
  have h9 : Real.sqrt 36 = 6 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h8, h9]