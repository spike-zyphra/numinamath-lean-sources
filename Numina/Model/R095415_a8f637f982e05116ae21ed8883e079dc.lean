import Mathlib

theorem algebra_305766 :
    IsGreatest {y : ℝ | ∃ x, x^2 + 2 * y^2 - 2 * x * y + x - 3 * y + 1 = 0} (3 / 2) := by
  constructor 
  · -- Show 3/2 is in the set.
    use 1
    norm_num
  · -- Show that 3/2 is the greatest element.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h : x^2 + 2 * y^2 - 2 * x * y + x - 3 * y + 1 = 0 := by linarith
    nlinarith [sq_nonneg (x + (-2 * y + 1) / 2)]