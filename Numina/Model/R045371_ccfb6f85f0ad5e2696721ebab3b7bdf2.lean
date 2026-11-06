import Mathlib

open Real

theorem inequalities_9773 : IsLeast {a : ℝ | 0 < a ∧ ∀ x y : ℝ, 0 < x → 0 < y → (x + y) * (1 / x + a / y) ≥ 9} 4 := by
  constructor
  · -- Show 4 is in the set
    constructor
    · norm_num
    · intro x y hx hy
      have h1 : (x + y) * (1 / x + (4: ℝ) / y) ≥ 9 := by
        have h2 : x > 0 := hx
        have h3 : y > 0 := hy
        have h4 : (x + y) * (1 / x + (4: ℝ) / y) = 5 + y / x + 4 * x / y := by
          field_simp
          ring
        rw [h4]
        have h5 : y / x + 4 * x / y ≥ 4 := by
          have h6 : x > 0 := hx
          have h7 : y > 0 := hy
          have h8 : y / x + 4 * x / y - (4: ℝ) ≥ 0 := by
            have h9 : y / x + 4 * x / y - (4: ℝ) = (y^2 + 4 * x^2 - 4 * x * y) / (x * y) := by 
              field_simp
              ring
            rw [h9]
            have h10 : y^2 + 4 * x^2 - 4 * x * y ≥ 0 := by 
              have h11 : (y - 2 * x) ^ 2 ≥ 0 := sq_nonneg (y - 2 * x)
              linarith
            have h11 : x * y > 0 := mul_pos hx hy
            apply div_nonneg
            linarith
            all_goals linarith
          linarith
        linarith
      linarith
  · -- Show that 4 is the minimal element
    intro a ha
    rcases ha with ⟨ha_pos, h⟩
    have h4 := h 1 2 (by norm_num) (by norm_num)
    norm_num at h4 
    linarith