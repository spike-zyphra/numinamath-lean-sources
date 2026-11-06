import Mathlib

theorem algebra_284264 :
  {(x, y) : ℝ × ℝ | 
    x > 0 ∧ y > 0 ∧
    x * (1 + 0.000011 * 100) + y * (1 + 0.000031 * 100) = 1.0024 ∧
    x + y = 1} =
  {(0.35, 0.65)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume the point is in the left side set, prove it is in the right side set.
    rintro ⟨hx, hy, heq1, heq2⟩
    norm_num at heq1 heq2
    have h1 : x = (0.35 : ℝ) := by
      nlinarith
    have h2 : y = (0.65 : ℝ) := by
      linarith [h1, heq2]
    simp [h1, h2]
  · -- Assume the point is in the right side set, prove it is in the left side set.
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num