import Mathlib

theorem algebra_18925 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 14 * x + 3) :
    IsLeast {x | ∃ y, f x = y ∧ ∀ x', f x' ≥ y} 7 := by
  constructor
  · -- Show that 7 belongs to the set
    use -46
    constructor
    · -- Verify that f 7 = -46
      rw [hf]
      norm_num
    · -- Show that -46 is the minimum value
      intro x'
      rw [hf]
      simp
      have h : (x' - 7) ^ 2 ≥ 0 := by
        apply sq_nonneg
      linarith
  · -- Show that no smaller element belongs to the set
    intro x hx
    rcases hx with ⟨y, hfx, hmin⟩
    have h1 := hmin 7
    simp [hf] at hfx h1 ⊢
    nlinarith [sq_nonneg (x - 7), sq_nonneg (x - 7)]