import Mathlib

theorem algebra_94 {a b : ℝ} (h : a * b = 1) :
    (1 / (1 + a) + 1 / (1 + b)) = (a / (1 + a) + b / (1 + b)) := by
  have h1 : a ≠ 0 := by
    by_contra h1
    have h2 : a * b = 0 := by
      rw [h1]
      norm_num
    linarith [h, h2]
  have h2 : b ≠ 0 := by
    by_contra h2
    have h3 : a * b = 0 := by
      rw [h2]
      norm_num
    linarith [h, h3]
  by_cases h1a : 1 + a = 0
  · -- Suppose 1 + a = 0, then a = -1, and b = -1 from ab = 1
    have ha : a = -1 := by linarith
    have hb : b = -1 := by
      rw [ha] at h
      linarith
    rw [ha, hb]
    norm_num
  · -- Suppose 1 + b = 0, then b = -1, and a = -1 from ab = 1
    by_cases h1b : 1 + b = 0
    · -- Suppose 1 + b = 0, then b = -1, and a = -1 from ab = 1
      have hb : b = -1 := by linarith
      have ha : a = -1 := by
        rw [hb] at h
        linarith
      rw [ha, hb]
      norm_num
    · -- Assume neither 1 + a = 0 nor 1 + b = 0
      have h1a' : 1 + a ≠ 0 := by
        exact h1a
      have h1b' : 1 + b ≠ 0 := by
        exact h1b
      field_simp [(show 1 + a ≠ 0 by exact h1a'), (show 1 + b ≠ 0 by exact h1b')]
      <;> nlinarith [h]