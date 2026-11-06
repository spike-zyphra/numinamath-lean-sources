import Mathlib

theorem algebra_3583 : IsLeast {t : ℝ | ∃ x y, t = 10*x^2 + 12*x*y + 5*y^2 - 4*x + 6*y + 2017} 2004 := by
  constructor
  · -- Show that 2004 is in the set
    use 2, -3
    norm_num
  · -- Show that 2004 is the least in the set 
    intro t ht
    rcases ht with ⟨x, y, h_eq⟩
    have h1 : 10*x^2 + 12*x*y + 5*y^2 - 4*x + 6*y + 2017 ≥ 2004 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 3),
          sq_nonneg (x + (3 * y - 1)/5), sq_nonneg (y + 3)]
    linarith [h_eq, h1]