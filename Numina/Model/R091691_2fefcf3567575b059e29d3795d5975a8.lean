import Mathlib

theorem algebra_21490 : IsLeast {x : ℝ | (x + 2) / 3 = 4 / (x + 1)} (-5) := by
  constructor
  · -- Show that -5 is indeed in the set
    norm_num
  · -- Show that -5 is the smallest element in the set
    intro y hy
    have h : (y + 2) / 3 = 4 / (y + 1) := by
      simpa using hy
    have h1 : y + 1 ≠ 0 := by
      by_contra h2
      have h3 : y = -1 := by linarith
      rw [h3] at h
      norm_num at h
    field_simp [h1] at h
    have h2 : y^2 + 3 * y - 10 = 0 := by
      nlinarith
    have h3 : (y - 2) * (y + 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- Case where y = 2, which is greater than -5
      linarith
    · -- Case where y = -5, which is the smallest
      linarith