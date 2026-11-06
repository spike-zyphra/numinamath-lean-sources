import Mathlib

open Real Set

theorem calculus_81585 (f : ℝ → ℝ) (hf : f = fun x => (2 * x ^ 2 + 98) / (x + 7) ^ 2) :
    IsLeast {y | ∃ x, y = f x ∧ x ≠ -7} 1 := by
  constructor
  · -- Show 1 is in the set.
    use 7
    constructor
    · -- Verify f(7) = 1.
      rw [hf]
      norm_num
    · -- Verify 7 ≠ -7.
      norm_num
  · -- Show 1 is the smallest in the set.
    intro y hy
    rcases hy with ⟨x, hfx, hx⟩
    rw [hfx]
    rw [hf]
    have h1 : x ≠ -7 := hx
    have h2 : (2 * x ^ 2 + 98) / (x + 7) ^ 2 ≥ 1 := by
      have hx1 : x + 7 ≠ 0 := by
        intro h
        apply h1
        linarith
      have hx2 : (x + 7) ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        exact hx1
      have h3 : 2 * x ^ 2 + 98 ≥ (x + 7) ^ 2 := by
        nlinarith [sq_nonneg (x - 7)]
      have h4 : (2 * x ^ 2 + 98) / (x + 7) ^ 2 ≥ ( (x + 7) ^ 2 ) / (x + 7) ^ 2 := by
        apply (div_le_div_right hx2).mpr
        linarith [h3]
      have h5 : ( (x + 7) ^ 2 ) / (x + 7) ^ 2 = 1 := by
        field_simp [hx1]
      linarith [h4, h5]
    simpa using h2