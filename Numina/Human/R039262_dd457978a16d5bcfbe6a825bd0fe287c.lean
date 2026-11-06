import Mathlib

theorem algebra_302424 (f : ℝ → ℝ) (hf : f = fun x => x^4 + 4 * x + 4) :
    IsLeast {y | ∃ x, f x = y} 1 := by
  -- We need to prove that 1 is the least element of the set {y | ∃ x, f x = y}.
  constructor
  -- First, let's show that 1 is in the set.
  · rw [Set.mem_setOf_eq]
    use -1
    norm_num [hf]
  -- Then, we need to show that 1 is a lower bound for the set.
  · intro y hy
    rcases hy with ⟨x, hx⟩
    simp [hf] at hx
    have heq : x ^ 4 + 4 * x + 4 = (x ^ 2 - 1) ^ 2 + 2 * (x + 1) ^ 2 + 1 := by ring
    rw [← hx, heq]
    linarith only [sq_nonneg (x ^ 2 - 1), sq_nonneg (x + 1)]
