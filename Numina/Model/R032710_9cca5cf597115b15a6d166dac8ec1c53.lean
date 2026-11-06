import Mathlib

theorem algebra_270412 {f : ℝ → ℝ} (hf : f = fun x => x^2 - x + 1) :
    ∃! x, f (f (f x)) = x := by
  use 1
  constructor
  · -- Show that $1$ is a solution. 
    rw [hf]
    norm_num
  · -- Show that it is the unique solution
    intro x h
    rw [hf] at h
    simp at h
    have h1 : x = 1 := by
      nlinarith [sq_nonneg (x - 1), sq_nonneg ((x ^ 2 - x + 1) - 1), sq_nonneg (((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1) + 1) - 1), sq_nonneg (x ^ 2 - x), sq_nonneg ((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1)), sq_nonneg (((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1) + 1) ^ 2 - ((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1) + 1)), sq_nonneg (x - 1), sq_nonneg ((x ^ 2 - x + 1) - (x)), sq_nonneg (((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1) + 1) - (x ^ 2 - x + 1)), sq_nonneg (((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1) + 1) ^ 2 - ((x ^ 2 - x + 1) ^ 2 - (x ^ 2 - x + 1) + 1))]
    linarith