import Mathlib

theorem algebra_94241 :
IsLeast {t : ℝ | ∃ x y, t = (x * y - 1)^2 + (x + y)^2} 1 := by
  constructor
  · -- Show that 1 is in the set, so there exists x, y such that (x*y - 1)^2 + (x+y)^2 = 1
    use 0, 0
    norm_num
  · -- Show that if t is in the set, then t >= 1
    intro t ht
    rcases ht with ⟨x, y, hx⟩
    -- We need to prove that t >= 1 from the existence of x and y such that h includes them
    nlinarith [sq_nonneg (x * y - 1), sq_nonneg (x + y), sq_nonneg (x * y), sq_nonneg (x^2 * y^2), sq_nonneg (x^2), sq_nonneg (y^2), sq_nonneg (x * y * x), sq_nonneg (x * y * y)]