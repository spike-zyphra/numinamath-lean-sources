import Mathlib

theorem algebra_6686 : IsGreatest { -x^2 + 14 * x - 25 | x : ℝ } 24 := by
  constructor
  · -- Show that 24 is indeed in the set by finding a value of x that gives 24
    use 7
    norm_num
  · -- Show that 24 is the greatest value in the set
    intro y
    rintro ⟨x, hx⟩
    have h : -x^2 + 14 * x - 25 ≤ 24 := by
      nlinarith [sq_nonneg (x - 7)]
    linarith