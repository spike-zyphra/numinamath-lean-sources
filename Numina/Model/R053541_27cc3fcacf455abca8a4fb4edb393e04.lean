import Mathlib

open Real Set

theorem algebra_194340 (c : ℝ → ℝ) (hc : c = fun x => 2 - x + 2 * sqrt (x - 1)) :
    IsGreatest (image c {x | 1 < x}) 2 := by
  constructor
  · -- Show that 2 is in the image of c, which gives us 2 ∈ {x | 1 < x}
    use 2
    constructor
    · -- Show that 2 is in the domain {x | 1 < x}
      norm_num
    · -- Show that c 2 = 2
      have h1 : ∀ x, c x = 2 - x + 2 * sqrt (x - 1) := by
        intro x
        rw [hc]
      rw [h1]
      have h2 : sqrt (2 - 1 : ℝ) = 1 := by
        rw [show (2 - 1 : ℝ) = 1 by norm_num]
        exact Real.sqrt_one
      simp [h2]
      all_goals norm_num
  · -- Show that 2 is greatest
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    have h1 : ∀ x, c x = 2 - x + 2 * sqrt (x - 1) := by
      intro x
      rw [hc]
    have hx1 : 1 < x := hx
    rw [show y = c x by linarith [hfx]]
    have h2 : c x = 2 - x + 2 * sqrt (x - 1) := h1 x
    rw [h2]
    have h4 : 0 ≤ x - 1 := by linarith
    have h5 : 0 ≤ sqrt (x - 1) := Real.sqrt_nonneg (x - 1)
    nlinarith [Real.sqrt_nonneg (x - 1), Real.sq_sqrt (show 0 ≤ x - 1 by linarith), sq_nonneg (sqrt (x - 1) - 1), sq_nonneg (x - 2)]