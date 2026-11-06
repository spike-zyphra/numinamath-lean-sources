import Mathlib

theorem algebra_301297 (a b : ℝ) (ha : a < b) (f : ℝ → ℝ) (hf : f = fun x => abs (x - a) + abs (x - b)) :
    IsLeast (Set.image f (Set.Icc a b)) (b - a) := by
  constructor
  · -- Show that b - a is achieved at some point in the interval [a, b].
    use b
    constructor
    · -- Show that b ∈ [a, b].
      exact ⟨by linarith, by linarith⟩
    · -- Calculate f(b).
      rw [hf]
      simp
      all_goals
      try linarith
  · -- Show that b - a is indeed the smallest value.
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have hx1 : a ≤ x := by
      have h1 : x ∈ Set.Icc (a : ℝ) (b : ℝ) := hx
      exact h1.1
    have hx2 : x ≤ b := by
      have h1 : x ∈ Set.Icc (a : ℝ) (b : ℝ) := hx
      exact h1.2
    rw [hf] at hfx
    simp at hfx
    have h3 : abs (x - a) = x - a := by
      rw [abs_of_nonneg]
      linarith
    have h4 : abs (x - b) = b - x := by
      rw [abs_of_nonpos]
      linarith
      all_goals linarith
    rw [h3, h4] at hfx
    linarith