import Mathlib

theorem algebra_187280 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h1 : 2 * (Real.sqrt x + Real.sqrt y) = 3 * Real.sqrt (x * y)) (h2 : x + y = 5) :
    (x = 4 ∧ y = 1) ∨ (x = 1 ∧ y = 4) := by 
  have h3 : 0 ≤ Real.sqrt x := by positivity
  have h4 : 0 ≤ Real.sqrt y := by positivity 
  have h5 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (show 0 ≤ x by linarith)
  have h6 : Real.sqrt y ^ 2 = y := Real.sq_sqrt (show 0 ≤ y by linarith)
  have h7 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by 
    rw [Real.sqrt_mul (by linarith)]
  rw [h7] at h1
  have eq1 : (Real.sqrt x + Real.sqrt y) ^ 2 = 5 + 2 * (Real.sqrt x * Real.sqrt y) := by
    have h10 : (Real.sqrt x + Real.sqrt y) ^ 2 = Real.sqrt x ^2 + Real.sqrt y ^ 2 + 2 * (Real.sqrt x * Real.sqrt y) := by ring
    rw [h10]
    have h11 : Real.sqrt x ^2 = x := h5
    have h12 : Real.sqrt y ^2 = y := h6
    rw [h11, h12]
    have h13 : x + y = 5 := h2
    nlinarith 
  have eq3 : (Real.sqrt x + Real.sqrt y) = 3 := by
    nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg ((Real.sqrt x + Real.sqrt y) - 3), h1, eq1, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), Real.sqrt_nonneg x, Real.sqrt_nonneg y]
  have eq4 : (Real.sqrt y) = 3 - Real.sqrt x := by linarith
  have eq5 : (Real.sqrt x - 1) * (Real.sqrt x - 2) = 0 := by
    rw [eq4] at h1
    nlinarith [Real.sqrt_nonneg x, sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt x - 2), h1, sq_nonneg (Real.sqrt x ^ 2 - 1), sq_nonneg (Real.sqrt x ^ 2 - 4)]
  cases' (mul_eq_zero.mp eq5) with eq6 eq7
  · -- case Real.sqrt x = 1
    have h8 : Real.sqrt x = 1 := by linarith
    have hx1 : x = 1 := by 
      calc 
        x = Real.sqrt x ^2 := by linarith [h5]
        _ = 1 ^2 := by rw [h8]
        _ = 1 := by norm_num
    have hy4 : y = 4 := by linarith [h2, hx1]
    right 
    exact ⟨hx1, hy4⟩
  · -- case Real.sqrt x = 2
    have h9 : Real.sqrt x = 2 := by linarith
    have hx4 : x = 4 := by 
      calc 
        x = Real.sqrt x ^2 := by linarith [h5]
        _ = 2 ^2 := by rw [h9]
        _ = 4 := by norm_num
    have hy1 : y = 1 := by linarith [h2, hx4]
    left 
    exact ⟨hx4, hy1⟩