import Mathlib

theorem algebra_304879 {a b : ℝ} (ha : a * b = 1) (hb : a ≠ 1)
    (M N : ℝ) (hM : M = a / (a + 1) + b / (b + 1)) (hN : N = 1 / (a + 1) + 1 / (b + 1)) :
    M - N = 0 := by
  rw [hM, hN]
  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    simp at ha
  have h2 : b ≠ 0 := by
    by_contra h
    rw [h] at ha
    simp at ha
  -- Case analysis: either a + 1 = 0 or not
  by_cases h4 : a + 1 = 0
  · -- If a + 1 = 0 then a = -1, and since a * b = 1, b must equals -1.
    have ha1 : a = -1 := by linarith
    have hb1 : b = -1 := by
      rw [ha1] at ha
      nlinarith
    rw [ha1, hb1]
    norm_num
  · -- Assume a + 1 ≠ 0, then b + 1 ≠ 0
    have h3 : b + 1 ≠ 0 := by
      by_contra h
      have h5 : b = -1 := by linarith
      rw [h5] at ha
      have ha1 : a = -1 := by nlinarith
      have h6 : a + 1 = 0 := by linarith
      contradiction
    field_simp [h4, h3]
    nlinarith [ha]