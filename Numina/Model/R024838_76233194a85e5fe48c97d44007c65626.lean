import Mathlib.Tactic

theorem algebra_1165 (x : ℝ) (h : ∑ i ∈ Finset.range 1006, x / ((2 * i + 2) * (2 * i + 4)) = 503 / 1007) :
    x = 2 := by

  -- We first prove a formula for the sum through induction
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, x / ((2 * i + 2) * (2 * i + 4)) = x / 4 * (1 - 1 / (n + 1 : ℝ)) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp at *
      ring

  -- Apply the formula to n = 1006
  specialize h1 1006
  rw [h1] at h

  -- Simplify the equation and solve for x
  field_simp at h
  ring_nf at h
  linarith