import Mathlib

theorem algebra_196394 (f : ℝ → ℝ) (hf : f = fun x => abs (x^2 - 4) - 6 * x) :
    IsGreatest {y | ∃ x, x ∈ Set.Icc (-2) 5 ∧ f x = y} 12 := by
  constructor
  · -- Show that 12 is in the set
    use -2
    constructor
    · norm_num [Set.mem_Icc]
    · -- Compute f(-2)
      rw [hf]
      norm_num [abs_of_nonneg]
  · -- Show that 12 is the greatest
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx
    simp at hfx
    rw [Set.mem_Icc] at hx
    rcases hx with ⟨hx1, hx2⟩
    by_cases h : x^2 - 4 ≥ 0
    · -- Case where x^2 -4 ≥ 0, so |x^2-4| = x^2-4
      rw [abs_of_nonneg h] at hfx
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 2)]
    · -- Case where x^2 -4 < 0, so |x^2-4| = 4-x^2
      rw [abs_of_neg (not_le.mp h)] at hfx
      nlinarith [sq_nonneg (x + 3), sq_nonneg (x - 5)]