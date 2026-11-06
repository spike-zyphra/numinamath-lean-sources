import Mathlib

theorem algebra_243582 {x y : ℝ}
    (h1 : 16*x^2+8*x*y+4*y^2+20*x+2*y=-7) (h2 : 8*x^2-16*x*y+2*y^2+20*x-14*y=-11) :
    x=-3/4 ∧ y=1/2 := by
  have h3 : (x + 3/4)^2 + (y - 1/2)^2 = 0 := by
    nlinarith [sq_nonneg (x + 3/4), sq_nonneg (y - 1/2), sq_nonneg (2*x - y), sq_nonneg (4*x + y)]
  have hx : x = -3/4 := by
    nlinarith [sq_nonneg (x + 3/4), sq_nonneg (y - 1/2)]
  have hy : y = 1/2 := by
    nlinarith [sq_nonneg (x + 3/4), sq_nonneg (y - 1/2)]
  exact ⟨hx, hy⟩