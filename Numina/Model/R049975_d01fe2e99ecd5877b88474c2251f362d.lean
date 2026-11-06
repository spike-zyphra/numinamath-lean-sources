import Mathlib

theorem algebra_15252 (f : ℝ → ℝ) (hf : f = fun x => x ^ 4 - 34 * x ^ 2 + 225) :
    IsLeast {x | f x = 0} (-5) := by 
  constructor
  · -- Show -5 is a solution
    rw [Set.mem_setOf_eq]
    rw [hf]
    norm_num
  · -- Show that -5 is the smallest
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    rw [hf] at hx
    simp at hx
    nlinarith [sq_nonneg (x ^ 2 - 25), sq_nonneg (x ^ 2 - 9), sq_nonneg (x + 5), sq_nonneg (x - 5), sq_nonneg (x + 3), sq_nonneg (x - 3)]