import Mathlib

theorem algebra_243690 (x y : ℝ) (h1 : 4*x^2+8*x*y+16*y^2+2*x+20*y=-7) (h2 : 2*x^2-16*x*y+8*y^2-14*x+20*y=-11) :
    x=1/2 ∧ y=-3/4 := by
  have h3 : (x - 1/2)^2 + (y + 3/4)^2 = 0 := by
    nlinarith [sq_nonneg (x - 1/2), sq_nonneg (y + 3/4)]
  have h4 : (x - 1/2)^2 = 0 := by
    nlinarith [sq_nonneg (y + 3/4)]
  have h5 : (y + 3/4)^2 = 0 := by
    nlinarith [sq_nonneg (x - 1/2)]
  have hx : x = 1/2 := by
    nlinarith [pow_eq_zero h4]
  have hy : y = -3/4 := by
    nlinarith [pow_eq_zero h5]
  exact ⟨hx, hy⟩