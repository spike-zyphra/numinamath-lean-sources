import Mathlib

theorem algebra_20143 : IsGreatest {-x^2 - 8 * x + 12 | x : ℝ} 28 := by
  constructor
  · -- Show 28 is in the set.
    use -4
    norm_num
  · -- Show that no value greater than 28 is in the set.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h : -x^2 - 8 * x + 12 ≤ 28 := by
      nlinarith [sq_nonneg (x + 4)]
    linarith