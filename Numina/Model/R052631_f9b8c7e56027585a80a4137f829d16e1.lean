import Mathlib

theorem algebra_172529 (f : ℝ → ℝ) (hf : f = fun x => x^6 - 6 * x) :
    IsLeast (Set.image f (Set.univ : Set ℝ)) (-5) := by
  constructor
  · -- Show that -5 is attained by f
    use 1
    simp [hf]
    norm_num
  · -- Show that -5 is the least value
    intro y
    intro hy
    rcases hy with ⟨x, hx⟩
    simp [hf] at hx
    have h : x ^ 6 - 6 * x ≥ -5 := by
      nlinarith [sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x ^ 3 + 1), sq_nonneg (x ^ 2 + 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - x + 1), sq_nonneg (x ^ 2 + x + 1), sq_nonneg (x ^ 3 - x ^ 2), sq_nonneg (x ^ 3 + x ^ 2)]
    linarith