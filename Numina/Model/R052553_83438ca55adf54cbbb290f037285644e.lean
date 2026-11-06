import Mathlib

theorem algebra_246487 (x : ℝ) (hx : 0 < x) :
    ∃! y : ℝ, 0 < y ∧ y < 1 ∧ x = y / (1 - y) := by
  use x / (1 + x)
  constructor
  · -- Verify that 0 < y, y < 1 and x = y / (1 - y).
    constructor
    · -- Show that 0 < x / (1 + x).
      apply div_pos
      linarith
      linarith
    constructor
    · -- Show that x / (1 + x) < 1.
      have h1 : x / (1 + x) < 1 := by 
        have h2 : 0 < 1 + x := by linarith 
        apply (div_lt_iff₀ h2).mpr 
        nlinarith 
      linarith 
    · -- Verify that x = y / (1 - y).
      field_simp [(show 1 + x ≠ 0 by linarith), (show 1 - x / (1 + x) ≠ 0 by 
        have h1 : 0 < x := hx 
        have h2 : 0 < 1 + x := by nlinarith 
        have h3 : x / (1 + x) < 1 := by 
          have h4 : 0 < 1 + x := by nlinarith 
          apply (div_lt_iff₀ h4).mpr 
          nlinarith 
        nlinarith 
      )]
      <;> nlinarith 
  · -- Verify that y is unique.
    intro y' ⟨hy_pos, hy_lt_1, hx_eq⟩ 
    have eq1 : y' / (1 - y') = x := by linarith 
    have eq2 : y' = x / (1 + x) := by 
      have h1 : 1 - y' ≠ 0 := by 
        linarith 
      field_simp [h1] at eq1 ⊢ 
      <;> nlinarith 
    have eq3 : y' = x / (1 + x) := eq2 
    linarith [eq3]