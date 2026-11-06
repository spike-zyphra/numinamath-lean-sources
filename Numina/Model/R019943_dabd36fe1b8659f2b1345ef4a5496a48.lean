import Mathlib

theorem algebra_161547 (x y z : ℝ) :
    x > 0 ∧ y > 0 ∧ z > 0 ↔ x + y + z > 0 ∧ x * y + y * z + x * z > 0 ∧ x * y * z > 0 := by
  constructor
  · -- Forward direction: if x,y,z > 0, all inequalities hold
    rintro ⟨hx, hy, hz⟩
    constructor
    · -- Show x + y + z > 0
      nlinarith
    constructor
    · -- Show x * y + y * z + x * z > 0
      nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
    · -- Show x * y * z > 0
      positivity
  · -- Backward direction: if all inequalities hold, x,y,z > 0
    rintro ⟨h1, h2, h3⟩
    constructor
    · -- Show x > 0
      by_contra h
      push_neg at h
      have h4 : x ≤ (0 : ℝ) := h
      nlinarith [sq_nonneg (x), sq_nonneg (y + z), sq_nonneg (y - z), sq_nonneg (x + y + z), sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]
    constructor
    · -- Show y > 0
      by_contra h
      push_neg at h
      have h4 : y ≤ (0 : ℝ) := h
      nlinarith [sq_nonneg (y), sq_nonneg (x + z), sq_nonneg (x - z), sq_nonneg (x + y + z), sq_nonneg (y), sq_nonneg (x), sq_nonneg (z)]
    · -- Show z > 0
      by_contra h
      push_neg at h
      have h4 : z ≤ (0 : ℝ) := h
      nlinarith [sq_nonneg (z), sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x + y + z), sq_nonneg (z), sq_nonneg (x), sq_nonneg (y)]