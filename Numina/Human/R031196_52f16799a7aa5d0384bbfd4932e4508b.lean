import Mathlib

/- Given that the solution set of the quadratic inequality $x^{2}-4x+a^{2}\leqslant 0$ concerning $x$ is empty, find the range of values for the real number $a$. -/
theorem algebra_9311 (a : ℝ) :
    {x | x^2 - 4 * x + a^2 ≤ 0} = ∅ ↔ a < -2 ∨ a > 2 := by

  -- Split the goal into two directions
  constructor <;> intro h

  -- Direction 1:
  -- Assume {x | x ^ 2 - 4 * x + a ^ 2 ≤ 0} = ∅
  -- Show a < -2 ∨ a > 2
  .
    -- The assumption is equivalent to:
    -- ∀ x, x^2 - 4 * x + a^2 > 0
    replace h : ∀ x, x^2 - 4 * x + a^2 > 0 := by
      intro x
      apply_fun (x ∈ ·) at h
      simp at h
      assumption

    -- Plug in x = 2
    specialize h 2

    -- Trivial but tedious steps
    replace h : 2^2 < a^2 := by linarith
    rw [sq_lt_sq] at h
    contrapose! h
    simp
    exact abs_le.2 h

  -- Direction 2:
  -- Assume a < -2 ∨ a > 2
  -- Show {x | x ^ 2 - 4 * x + a ^ 2 ≤ 0} = ∅
  .
    -- The goal is equivalent to:
    -- ∀ x, x^2 - 4 * x + a^2 > 0
    ext x
    simp

    -- The assumption is equivalent to:
    -- 2^2 < a^2
    replace h : 2^2 < a^2 := by
      rw [sq_lt_sq]
      cases h with
      | inl h =>
        have h1 : a < 0 := by linarith
        simp [abs_of_neg h1]
        linarith
      | inr h =>
        have h2 : a > 0 := by linarith
        simp [abs_of_pos h2]
        linarith

    -- We also have:
    -- x^2 - 4*x + 4 = (x - 2)^2 ≥ 0
    have h1 : x^2 - 4*x + 4 ≥ 0 := by
      calc
        x^2 - 4*x + 4 = (x - 2)^2 := by ring
                    _ ≥ 0 := by apply sq_nonneg

    -- Combine the two inequalities
    linarith
