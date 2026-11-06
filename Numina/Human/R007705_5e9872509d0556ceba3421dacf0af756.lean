import Mathlib

/-Find the solution set for the inequality $x^2 < x$.-/
theorem algebra_9347 (x : ℝ) : x ^ 2 < x ↔ x ∈ Set.Ioo 0 1 := by
  -- Now, we factor the left side as $x(x - 1) < 0$.
  rw [←sub_neg, show x^2 - x = x * (x - 1) by nlinarith]
  constructor <;> intro h
  · -- The inequality $x(x - 1) < 0$ holds true only in the interval where the
    -- expression evaluates to a negative value, which, based on our tests, is when $0 < x < 1$.
    rcases mul_neg_iff.1 h with pos | neg
    · simp [pos]; linarith
    · simp at neg; linarith
  · simp at h
    exact mul_neg_iff.2 (Or.inl ⟨h.1, by linarith⟩)
