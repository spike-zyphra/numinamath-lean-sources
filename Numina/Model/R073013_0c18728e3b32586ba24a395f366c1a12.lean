import Mathlib

theorem algebra_318695 (f : ℝ → ℝ) (hf : f = fun x => x * abs x - 2 * x + 1) :
    IsGreatest (Set.image f (Set.Icc (-7) 5)) 16 := by
  constructor
  · -- Show that 16 is in the image
    use 5
    constructor
    · norm_num
    · -- Compute f 5
      rw [hf]
      norm_num [abs_of_nonneg]
  · -- Show that any value in the image is ≤ 16
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    simp at hfx
    have hx1 : -7 ≤ x := by
      have h1 : x ∈ Set.Icc (-7 : ℝ) (5 : ℝ) := by simpa using hx
      exact h1.left
    have hx2 : x ≤ 5 := by
      have h1 : x ∈ Set.Icc (-7 : ℝ) (5 : ℝ) := by simpa using hx
      exact h1.right
    by_cases h : 0 ≤ x
    · -- If x ≥ 0, |x| = x
      rw [abs_of_nonneg h] at hfx
      nlinarith [sq_nonneg (x - 5), sq_nonneg (x - 1)]
    · -- x < 0
      have h' : x < 0 := by linarith
      rw [abs_of_neg (show x < 0 by linarith)] at hfx
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 5), sq_nonneg (x), sq_nonneg (x + 7)]