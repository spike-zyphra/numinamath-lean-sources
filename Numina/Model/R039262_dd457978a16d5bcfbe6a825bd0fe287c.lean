import Mathlib

theorem algebra_302424 (f : ℝ → ℝ) (hf : f = fun x => x^4 + 4 * x + 4) :
    IsLeast {y | ∃ x, f x = y} 1 := by
  constructor
  · -- Show that 1 is in the image of the function
    use -1
    rw [hf]
    norm_num
  · -- Show that 1 is the least element in the image
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    nlinarith [sq_nonneg (x^2 + 2 * x + 1), sq_nonneg (x^2 - 2 * x + 1), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2 - 1)]