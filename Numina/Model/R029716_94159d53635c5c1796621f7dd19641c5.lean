import Mathlib

theorem algebra_309956 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : Real.sqrt x * (Real.sqrt x + 2 * Real.sqrt y) = Real.sqrt y * (6 * Real.sqrt x + 5 * Real.sqrt y)) :
    (x + Real.sqrt (x * y) - y) / (2 * x + Real.sqrt (x * y) + 3 * y) = 1 / 2 := by
  have h1 : 0 < Real.sqrt x := by
    apply Real.sqrt_pos.mpr
    exact hx
  have h2 : 0 < Real.sqrt y := by
    apply Real.sqrt_pos.mpr
    exact hy
  have h3 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h4 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
  have eq1 : Real.sqrt x ^ 2 - 4 * Real.sqrt x * Real.sqrt y - 5 * Real.sqrt y ^ 2 = 0 := by
    have eq2 : Real.sqrt x * (Real.sqrt x + 2 * Real.sqrt y) = Real.sqrt y * (6 * Real.sqrt x + 5 * Real.sqrt y) := by
      linarith [h]
    have eq3 : Real.sqrt x ^ 2 - 4 * Real.sqrt x * Real.sqrt y - 5 * Real.sqrt y ^ 2 = 0 := by
      have eq4 : Real.sqrt x * (Real.sqrt x + 2 * Real.sqrt y) = Real.sqrt x ^ 2 + 2 * Real.sqrt x * Real.sqrt y := by
        nlinarith
      have eq5 : Real.sqrt y * (6 * Real.sqrt x + 5 * Real.sqrt y) = 6 * Real.sqrt x * Real.sqrt y + 5 * Real.sqrt y ^ 2 := by
        nlinarith
      nlinarith [eq2, eq4, eq5]
    nlinarith [eq3, h3, h4]
  have eq3 : (Real.sqrt x - 5 * Real.sqrt y) * (Real.sqrt x + Real.sqrt y) = 0 := by
    nlinarith [eq1, h3, h4]
  cases' (mul_eq_zero.1 eq3) with h5 h6
  · -- Real.sqrt x - 5 * Real.sqrt y = 0
    -- So Real.sqrt x =5 * Real.sqrt y
    have h6 : Real.sqrt x = 5 * Real.sqrt y := by
      linarith
    have h7 : x = 25 * y := by
      have h8 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
      have h9 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith)
      have h10 : Real.sqrt x = 5 * Real.sqrt y := by
        linarith
      have h11 : Real.sqrt x ^ 2 = 25 * (Real.sqrt y ^ 2) := by
        rw [h10]
        nlinarith
      nlinarith [h8, h9, h11]
    have h8 : Real.sqrt (x * y) = 5 * y := by
      have h9 : x * y = (25 * y ^ 2) := by
        nlinarith [h7]
      rw [h9]
      have h10 : Real.sqrt (25 * y ^ 2) = 5 * y := by
        have h11 : Real.sqrt (25 * y ^ 2) = Real.sqrt (5 ^ 2 * y ^ 2) := by ring_nf
        rw [h11]
        have h12 : Real.sqrt ((5 * y) ^ 2) = 5 * y := by
          apply Real.sqrt_sq (by nlinarith)
        rw [show (5 ^ 2 * y ^ 2 : ℝ) = (5 * y) ^ 2 by ring] at *
        all_goals try linarith [h12, Real.sqrt_nonneg (5 * y ^ 2)]
      nlinarith [h10, Real.sqrt_nonneg (25 * y ^ 2)]
    have h9 : x + Real.sqrt (x * y) - y = 29 * y := by
      nlinarith [h8, h7]
    have h10 : (2 * x + Real.sqrt (x * y) + 3 * y) = 58 * y := by
      nlinarith [h8, h7]
    have h11 : (x + Real.sqrt (x * y) - y) / (2 * x + Real.sqrt (x * y) + 3 * y) = 1 / 2 := by
      rw [h9, h10]
      have h12 : y > 0 := by linarith
      field_simp
      <;> nlinarith
    exact_mod_cast h11
  · -- Real.sqrt x + Real.sqrt y = 0
    have h3 : Real.sqrt x + Real.sqrt y = 0 := by
      linarith
    have h4 : Real.sqrt x > 0 := h1
    have h5 : Real.sqrt y > 0 := h2
    have h6 : Real.sqrt x + Real.sqrt y > 0 := by
      linarith
    linarith