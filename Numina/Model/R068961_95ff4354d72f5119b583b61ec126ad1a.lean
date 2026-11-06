import Mathlib

theorem algebra_311423 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h : x * y = 20) (h' : (x - 6) * (y - 10) = 20 - 0.5 * x) :
    x = 4 ∧ y = 6 := by 
  have eq3 : x * y - 10 * x - 6 * y + 60 = 20 - 0.5 * x := by
    nlinarith [h']
  have eq4 : x * y = 20 := by
    linarith [h]
  rw [show x * y = 20 by linarith [eq4]] at eq3
  have h_eq4 : 9.5 * x + 6 * y = 60 := by
    ring_nf at eq3 ⊢
    nlinarith
  have h_eq5 : x = 4 := by
    nlinarith [h_eq4, h, sq_nonneg (x - 4), sq_nonneg (y - 6), mul_pos hx hy]
  have h_eq6 : y = 6 := by
    nlinarith [h, h_eq5]
  exact ⟨h_eq5, h_eq6⟩