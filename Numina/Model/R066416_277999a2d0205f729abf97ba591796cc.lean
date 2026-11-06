import Mathlib

open Real Set

theorem algebra_309614 (f : ℝ → ℝ) (hf : f = fun x => x^2 - x + 1 / x) :
    IsLeast {y | ∃ x > 0, f x = y} 1 := by
  constructor
  · -- Show 1 belongs to the set, with x = 1 > 0
    use 1
    constructor
    · -- Show 1 > 0
      norm_num
    · -- Show f 1 = 1
      rw [hf]
      norm_num
  · -- Show that 1 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx_pos, hfx_eq⟩
    rw [hf] at hfx_eq
    -- Use field simplification to handle fractions
    have h1 : x > 0 := hx_pos
    have h2 : x^2 - x + 1 / x ≥ 1 := by
      have h1 : x > 0 := hx_pos
      have h3 : x^2 - x + 1 / x - 1 ≥ 0 := by
        have h2_pos : x > 0 := hx_pos
        have h4 : x * (x^2 - x + 1 / x - 1) ≥ 0 := by
          have h6 : x * (x^2 - x + 1 / x - 1) = x^3 - x^2 + 1 - x := by
            field_simp
            <;> ring
          rw [h6]
          nlinarith [sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x * (x - 1)), sq_nonneg (x + 1 - 2), sq_nonneg (x * (x + 1 - 2)), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg (x + 1 - 3), sq_nonneg (x * (x^2 - 1)), hx_pos]
        have h2_pos : x > 0 := hx_pos
        -- Use positivity of x to remove denominator
        have h5 : x * (x^2 - x + 1 / x - 1) ≥ 0 := h4
        nlinarith [h5, hx_pos]
      linarith
    -- Since f x = y and f x ≥ 1, we have y ≥ 1
    have h3 : (x^2 - x + 1 / x) = y := by
      simp at hfx_eq ⊢
      all_goals
        try { field_simp at hfx_eq ⊢ }
        all_goals
          nlinarith
    linarith [h2, h3]
    all_goals nlinarith