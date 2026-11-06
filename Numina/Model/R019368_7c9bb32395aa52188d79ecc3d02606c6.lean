import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_304140 (f : ℝ → ℝ) (hf : f = λ x => 2 * x * (4 - x) * (3 - 2 * x)) :
    IsGreatest (image f (Set.Ioo 0 (3 / 2))) (200 / 27) := by
  constructor
  · -- Show that 200/27 is in the image of f over (0, 3/2)
    rw [mem_image]
    use 2 / 3
    constructor
    · -- Show that 2/3 is in (0, 3/2)
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that f(2/3) = 200/27
      rw [hf]
      norm_num
  · -- Show that 200/27 is the greatest value in the image
    intro y hy
    rw [mem_image] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [hf]
    simp at *
    rcases hx with ⟨hx0, hx1⟩
    nlinarith [sq_nonneg (x - 2 / 3), sq_nonneg (x - 1), sq_nonneg (x - 4 / 3), sq_nonneg (x * (x - 2 / 3)), sq_nonneg ((x - 2 / 3) * (4 - x - 5 / 3)), sq_nonneg ((x - 2 / 3) * (3 - 2 * x - 5 / 3)), mul_pos hx0 (by linarith : (3 / 2) - x > 0)]