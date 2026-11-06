import Mathlib

theorem algebra_254500 (f : ℝ → ℝ) (hf : f = fun x => 2 * x - 5 + Real.sqrt (11 - 3 * x)) :
    IsGreatest (Set.image f {x | 11 - 3 * x ≥ 0}) (65 / 24) := by
  constructor
  · -- Show that 65/24 is in the image of f on the domain
    use (167 / 48 : ℝ)
    constructor
    · -- Show that 167/48 is in the domain
      norm_num
    · -- Show that f(167/48) = 65/24
      rw [hf]
      have h1 : 11 - 3 * (167 / 48 : ℝ) = (9 / 16 : ℝ) := by
        norm_num
      have h2 : Real.sqrt (11 - 3 * (167 / 48 : ℝ)) = (3 / 4 : ℝ) := by
        rw [h1]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      simp [h2]
      norm_num
  · -- Show that 65/24 is the greatest value in the image
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx1 : 11 - 3 * x ≥ 0 := by
      simpa using hx
    rw [hf]
    simp at *
    nlinarith [sq_nonneg (Real.sqrt (11 - 3 * x) - (3 / 4 : ℝ)), 
        sq_nonneg ((11 - 3 * x) - (9 / 16 : ℝ)), 
        Real.sq_sqrt (show (0 : ℝ) ≤ 11 - 3 * x by linarith)]