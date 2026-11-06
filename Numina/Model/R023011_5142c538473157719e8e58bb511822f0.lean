import Mathlib

theorem algebra_243118 {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x > y)
    (h : (1 / 2) * (x + y) / Real.sqrt (x * y) = 5 / 4) :
    x / y = 4 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < Real.sqrt (x * y) := by
    apply Real.sqrt_pos.mpr
    all_goals linarith
  have h3 : (1 / 2) * (x + y) / Real.sqrt (x * y) = 5 / 4 := h
  have h4 : 4 * ((1 / 2) * (x + y)) = 5 * Real.sqrt (x * y) := by
    field_simp [h2] at h3 ⊢
    linarith
  have h5 : 2 * (x + y) = 5 * Real.sqrt (x * y) := by
    linarith [h4]
  have h6 : (2 * (x + y) ) ^ 2 = (25 * (x * y) ) := by
    calc 
      (2 * (x + y) ) ^ 2 = (5 * Real.sqrt (x * y) ) ^ 2 := by rw [h5]
      _ = 25 * (Real.sqrt (x * y) ^ 2) := by ring_nf
      _ = 25 * (x * y) := by rw [Real.sq_sqrt]; positivity
  have h7 : (4 * x ^ 2 - 17 * x * y + 4 * y ^ 2) = 0 := by
    nlinarith [h6, sq_pos_of_pos hx, sq_pos_of_pos hy]
  have h8 : (x - 4 * y) * (x - (1 / 4) * y) = 0 := by
    nlinarith [h7, sq_pos_of_pos hx, sq_pos_of_pos hy]
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- Case x - 4 * y = 0, so x = 4y
    have hx_eq : x = 4 * y := by linarith
    have hx_eq4 : x / y = 4 := by
      rw [hx_eq]
      field_simp [show 0 < y by linarith]
      <;> linarith
    exact hx_eq4
  · -- Case x - (1 / 4) * y = 0, so x = (1/4) * y
    have hx_eq : x = (1 / 4) * y := by linarith
    have h11 : x < y := by
      nlinarith [hx_eq, sq_pos_of_pos hx, sq_pos_of_pos hy]
    linarith [h11, show 0 < x by linarith, hxy]