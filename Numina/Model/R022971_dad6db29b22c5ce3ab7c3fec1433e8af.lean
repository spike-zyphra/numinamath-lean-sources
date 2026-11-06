import Mathlib

theorem algebra_231459 (f : ℝ → ℝ) :
    (∀ x, 2 * f (1 - x) + 1 = x * f x) ↔
    (∀ x, f x = (x - 3) / (x ^ 2 - x + 4)) := by
  constructor
  · -- Assume $f$ satisfies the functional equation, prove $f(x) = \frac{x-3}{x^2-x+4}$.
    intro h
    intro x
    have eq1 := h x
    have eq2 := h (1 - x)
    have eq3 : 2 * f x + 1 = (1 - x) * f (1 - x) := by
      have h1 := h (1 - x)
      have h2 : 1 - (1 - x) = x := by 
        ring
      rw [h2] at h1
      linarith
    -- Now, we have two equations:
    -- 1. `eq1`: $2 * f (1 - x) + 1 = x * f x$
    -- 2. `eq3`: $2 * f x + 1 = (1 - x) * f (1 - x)$
    -- Solving them simultaneously.
    have eq4 : f (1 - x) = (x * f x - 1) / 2 := by 
      linarith [eq1]
    rw [eq4] at eq3
    have h1 : f x = (x - 3) / (x ^ 2 - x + 4) := by 
      have h2 : (x ^ 2 - x + 4) * f x = x - 3 := by
        have h4 : 4 * f x + 2 = (1 - x) * (x * f x - 1) := by
          linarith [eq3]
        nlinarith [sq_nonneg (x * f x), sq_nonneg ((1 - x) - x), sq_nonneg (f x - 1)]
      have h5 : x ^ 2 - x + 4 ≠ 0 := by
        nlinarith [sq_nonneg (x - 1 / 2)]
      field_simp at h2 ⊢
      nlinarith
    simpa using h1
  · -- Assume $f(x) = \frac{x-3}{x^2-x+4}$, prove $2 f(1-x)+1=x f(x)$.
    intro hf x
    rw [hf (1 - x), hf x]
    field_simp [(show (x: ℝ) ^ 2 - x + 4 ≠ 0 by nlinarith [sq_nonneg (x - 1 / 2)]), 
                (show ((1 - x): ℝ) ^ 2 - (1 - x) + 4 ≠ 0 by nlinarith [sq_nonneg ((1 - x) - 1 / 2)])]
    ring