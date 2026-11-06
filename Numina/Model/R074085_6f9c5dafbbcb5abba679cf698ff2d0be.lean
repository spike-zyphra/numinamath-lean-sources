import Mathlib

theorem algebra_11057 (x : ℝ) : (3 + x) / (5 + x) = (1 + x) / (2 + x) ↔ x = 1 := by
  constructor
  · -- Assume (3 + x) / (5 + x) = (1 + x) / (2 + x) prove x = 1
    intro h
    have h1 : 5 + x ≠ 0 := by
      by_contra h2
      have h3 : x = -5 := by linarith
      rw [h3] at h
      norm_num at h
    have h2 : 2 + x ≠ 0 := by
      by_contra h3
      have h4 : x = -2 := by linarith
      rw [h4] at h
      norm_num at h
    field_simp [h1, h2] at h
    linarith
  · -- Assume x = 1 prove (3 + x) / (5 + x) = (1 + x) / (2 + x)
    intro h
    rw [h]
    norm_num