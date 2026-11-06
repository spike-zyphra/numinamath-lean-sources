import Mathlib

theorem algebra_10206 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 2 - 12 * x + 3) :
    IsLeast {x | ∃ y, f x = y ∧ ∀ z, f z ≥ y} 3 := by
  constructor
  · -- Show 3 is in the set
    use -15
    constructor
    · -- Show f 3 = -15
      rw [hf]
      norm_num
    · -- Show that ∀ (z : ℝ), f z ≥ -15
      intro z
      rw [hf]
      simp
      have h : 2 * z ^ 2 - 12 * z + 3 ≥ -15 := by
        nlinarith [sq_nonneg (z - 3)]
      linarith
  · -- Show that 3 is the least in the set
    intro x hx
    rcases hx with ⟨y, hfx, hmin⟩
    have h1 : f x = y := hfx
    have h2 := hmin 3
    have h3 : f 3 = -15 := by
      rw [hf]
      norm_num
    rw [h3] at h2
    have h4 : f x = y := hfx
    rw [hf] at h4
    simp at h4
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 3)]