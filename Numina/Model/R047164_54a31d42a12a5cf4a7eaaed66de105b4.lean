import Mathlib

theorem algebra_199952 {f : ℤ → ℤ}
    (h1 : f 1 + 1 > 0)
    (h2 : ∀ x y, f (x + y) - x * f y - y * f x = f x * f y - x - y + x * y)
    (h3 : ∀ x, 2 * f x = f (x + 1) - x + 1) :
    f 10 = 1014 := by
  have h4 : f 0 = 1 := by
    have h5 : f 0 * (f 0 - 1) = 0 := by
      specialize h2 0 0
      norm_num at h2
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- f 0 = 0
      exfalso
      have h8 : 2 * f 0 = f 1 - 0 + 1 := h3 0
      norm_num [show f 0 = (0 : ℤ) by linarith] at h8
      have h9 : f 1 = -1 := by linarith
      linarith
    · -- f 0 - 1 = 0
      linarith
  have h8 : 2 * f 0 = f 1 - 0 + 1 := h3 0
  simp [h4] at h8
  have h10 : f 1 = 1 := by linarith
  have h11 : 2 * f 1 = f 2 - 1 + 1 := h3 1
  simp [h10] at h11
  have h20 : f 2 = 2 := by linarith
  have h12 : 2 * f 2 = f 3 - 2 + 1 := h3 2
  simp [h20] at h12
  have h30 : f 3 = 5 := by linarith
  have h13 : 2 * f 3 = f 4 - 3 + 1 := h3 3
  simp [h30] at h13
  have h40 : f 4 = 12 := by linarith
  have h14 : 2 * f 4 = f 5 - 4 + 1 := h3 4
  simp [h40] at h14
  have h50 : f 5 = 27 := by linarith
  have h15 : 2 * f 5 = f 6 - 5 + 1 := h3 5
  simp [h50] at h15
  have h60 : f 6 = 58 := by linarith
  have h16 : 2 * f 6 = f 7 - 6 + 1 := h3 6
  simp [h60] at h16
  have h70 : f 7 = 121 := by linarith
  have h17 : 2 * f 7 = f 8 - 7 + 1 := h3 7
  simp [h70] at h17
  have h80 : f 8 = 248 := by linarith
  have h18 : 2 * f 8 = f 9 - 8 + 1 := h3 8
  simp [h80] at h18
  have h90 : f 9 = 503 := by linarith
  have h19 : 2 * f 9 = f 10 - 9 + 1 := h3 9
  simp [h90] at h19
  linarith