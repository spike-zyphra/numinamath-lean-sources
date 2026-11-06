import Mathlib
theorem algebra_607355 {x y : ℝ} : x * (x - 2 * y) + y * (2 * y - 4) + 4 = 0 ↔ x = 2 ∧ y = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2 and y = 2
    intro h
    have h1 : (x - y) ^ 2 + (y - 2) ^ 2 = 0 := by
      nlinarith
    have h2 : (x - y) ^ 2 = 0 := by
      linarith [sq_nonneg (x - y), sq_nonneg (y - 2)]
    have h3 : (y - 2) ^ 2 = 0 := by
      linarith [sq_nonneg (x - y), sq_nonneg (y - 2)]
    have h4 : y - 2 = 0 := by
      rwa [sq_eq_zero_iff] at h3
    have h5 : x - y = 0 := by
      rwa [sq_eq_zero_iff] at h2
    have hy : y = 2 := by
      linarith
    have hx : x = 2 := by
      linarith [hy, h5]
    constructor
    · exact hx
    · exact hy
  · -- Assume x = 2 and y = 2, prove the equation
    rintro ⟨hx, hy⟩
    rw [hx, hy]
    norm_num