import Mathlib

theorem algebra_22516 {x : ℝ} (hx : x ≠ -1) : (2*x^2 + x + 3)/(x^2 + x + 1) = (2*x + 1)/(x + 1) ↔ x = -2 := by
  constructor
  · -- Forward direction: equation implies x=-2
    intro h
    have h1 : x^2 + x + 1 ≠ 0 := by
      nlinarith [sq_nonneg (x + 0.5)]
    have h2 : x + 1 ≠ 0 := by 
      intro h3
      apply hx
      linarith 
    have eq1 : (2*x^2 + x + 3) * (x + 1) = (2*x + 1) * (x^2 + x + 1) := by 
      field_simp [(show x + 1 ≠ 0 by exact h2), (show x^2 + x + 1 ≠ 0 by exact h1)] at h ⊢
      nlinarith
    -- Now we have the polynomial equation.
    -- Expanding both sides and simplifying:
    have h3 : x + 2 = 0 := by
      nlinarith [eq1]
    linarith
  · -- Backward direction: x=-2 implies equation
    intro h
    rw [h]
    -- Check both sides by substituting x = -2.
    norm_num