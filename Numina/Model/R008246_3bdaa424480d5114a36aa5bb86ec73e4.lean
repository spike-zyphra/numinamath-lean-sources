import Mathlib

theorem algebra_12622 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + 12 * x + 5) :
    IsLeast {y | ∃ x, y = f x} (-31) := by
  constructor
  · -- Show that -31 is achievable, i.e., there exists an x such that f(x) = -31
    use -6
    rw [hf]
    -- Lean can compute f(-6) = (-6)^2 + 12 * (-6) + 5
    norm_num
  · -- Show that -31 is a lower bound for all y in the range of f
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    -- Now, we have y = x^2 + 12 * x + 5
    -- We can complete the square to show that y >= -31
    have h : (x + 6) ^ 2 ≥ 0 := by
      apply sq_nonneg
    linarith [h]