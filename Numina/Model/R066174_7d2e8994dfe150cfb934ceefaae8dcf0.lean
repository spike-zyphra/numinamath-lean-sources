import Mathlib

theorem algebra_21872 (x : ℝ) :
    (x ^ 2 + 11 * x + 28) / (x + 4) - 7 = x ↔ x ≠ -4 := by 
  constructor
  · -- Forward: equation implies x ≠ -4
    intro h
    by_contra h1
    have h2 : x = -4 := by linarith
    rw [h2] at h
    norm_num at h
  · -- Backward: x ≠ -4 implies equation holds
    intro h
    have h1 : x + 4 ≠ 0 := by 
      intro h2
      apply h
      linarith
    have eq1 : (x ^ 2 + 11 * x + 28) / (x + 4) = x + 7 := by 
      have h3 : x + 4 ≠ 0 := h1
      field_simp [h3]
      ring
    linarith [eq1]