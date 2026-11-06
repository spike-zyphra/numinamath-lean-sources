import Mathlib

theorem algebra_240775 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 600 * x + 369) :
    IsLeast {x | ∃ y, f x = y ∧ ∀ z, f z ≥ y} 300 := by
  constructor
  · -- Show 300 in the set
    use -89631
    constructor
    · -- Show that f 300 = - 89631
      rw [hf]
      norm_num
    · -- Show that ∀ (z : ℝ), f z ≥ - 89631
      intro z
      rw [hf]
      simp
      have h1 : (z) ^ 2 - 600 * (z) + 369 ≥ - 89631 := by
        nlinarith [sq_nonneg (z - 300)]
      linarith
  · -- Show that 300 is the least element in the set
    intro x hx
    rcases hx with ⟨y, hfx, hmin⟩
    have h1 : f x = y := hfx
    have h2 : ∀ z, f z ≥ y := hmin
    have h3 : f 300 ≥ y := h2 300
    -- Now compute f 300 and f x
    have eq1 : f x = x^2 - 600 * x + 369 := by
      rw [hf]
    have eq4 : f 300 = (300 : ℝ) ^ 2 - 600 * (300 : ℝ) + 369 := by
      rw [hf]
    have eq5 : f 300 = -89631 := by
      rw [eq4]
      norm_num
    -- Now from h3: f 300 >= y
    -- Therefore y <= -89631
    have eq6 : y ≤ -89631 := by
      linarith [h3, eq5]
    -- From h1: f x = y
    -- Therefore f x ≤ -89631
    have eq7 : f x ≤ -89631 := by
      linarith [h1, eq6]
    -- Now compute f x = x^2 - 600 x + 369
    rw [eq1] at eq7
    have h5 : (x - 300 : ℝ) ^ 2 ≤ 0 := by
      nlinarith
    have h6 : (x - 300 : ℝ) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 300 : ℝ)]
    have h7 : x - 300 = 0 := by
      nlinarith [h6, sq_nonneg (x - 300 : ℝ)]
    linarith