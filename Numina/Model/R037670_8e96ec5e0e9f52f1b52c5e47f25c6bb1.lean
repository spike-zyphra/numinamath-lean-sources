import Mathlib

open Real

theorem algebra_544 {x : ℝ} (hx1 : 0 ≤ x) (hx2 : x = √(6 + x)) : x = 3 := by
  have h1 : x ^ 2 = 6 + x := by
    have h_nonneg : 0 ≤ 6 + x := by
      nlinarith [hx1]
    calc x ^ 2 = (√(6 + x)) ^ 2 := by rw [←hx2]
      _ = 6 + x := Real.sq_sqrt h_nonneg
  have h2 : x ^ 2 - x - 6 = 0 := by linarith [h1]
  have h3 : (x - 3) * (x + 2) = 0 := by 
    nlinarith [h2]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · linarith [h4]
  · nlinarith [h5, hx1]