import Mathlib

theorem algebra_254500 (f : ℝ → ℝ) (hf : f = fun x => 2 * x - 5 + Real.sqrt (11 - 3 * x)) :
    IsGreatest (Set.image f {x | 11 - 3 * x ≥ 0}) (65 / 24) := by
  constructor
  · -- First, let's show 65/24 is in the image
    use 167 / 48
    have h1 : (167 / 48 : ℝ) ∈ {x | 11 - 3 * x ≥ 0} := by
      norm_num
    have h2 : Real.sqrt (11 - 3 * (167 / 48 : ℝ)) = 3 / 4 := by
      rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
    rw [hf]
    simp [h2]
    norm_num
  · -- Now, let's show 65/24 is an upper bound
    intro y
    rintro ⟨x, hx, hfx⟩
    have h1 : 11 - 3 * x ≥ 0 := by
      simpa using hx
    have h2 : Real.sqrt (11 - 3 * x) ≥ 0 := Real.sqrt_nonneg (11 - 3 * x)
    rw [hf] at hfx
    simp at hfx
    have h3 : (4 * Real.sqrt (11 - 3 * x) - 3) ^ 2 ≥ 0 := sq_nonneg (4 * Real.sqrt (11 - 3 * x) - 3)
    have h4 : (Real.sqrt (11 - 3 * x)) ^ 2 = 11 - 3 * x := by
      rw [Real.sq_sqrt]
      linarith
    nlinarith [sq_nonneg (4 * Real.sqrt (11 - 3 * x) - 3), h4]