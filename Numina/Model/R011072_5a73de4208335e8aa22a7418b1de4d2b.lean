import Mathlib

open Real

theorem algebra_10985
    (b : ℕ → ℕ)
    (hb0 : b 0 = 1)
    (hb1 : b 1 = 2)
    (hbn : ∀ n, b (n + 2) = b (n) * b (n + 1)) :
    b 19 = 2 ^ 4181 := by

  have h0 : b 0 = 1 := hb0
  have h1 : b 1 = 2 := hb1
  have h2 : b 2 = b 0 * b 1 := hbn 0
  simp [h0, h1] at h2
  have h3 : b 3 = b 1 * b 2 := hbn 1
  simp [h1, h2] at h3
  have h4 : b 4 = b 2 * b 3 := hbn 2
  simp [h2, h3] at h4
  have h5 : b 5 = b 3 * b 4 := hbn 3
  simp [h3, h4] at h5
  have h6 : b 6 = b 4 * b 5 := hbn 4
  simp [h4, h5] at h6
  have h7 : b 7 = b 5 * b 6 := hbn 5
  simp [h5, h6] at h7
  have h8 : b 8 = b 6 * b 7 := hbn 6
  simp [h6, h7] at h8
  have h9 : b 9 = b 7 * b 8 := hbn 7
  simp [h7, h8] at h9
  have h10 : b 10 = b 8 * b 9 := hbn 8
  simp [h8, h9] at h10
  have h11 : b 11 = b 9 * b 10 := hbn 9
  simp [h9, h10] at h11
  have h12 : b 12 = b 10 * b 11 := hbn 10
  simp [h10, h11] at h12
  have h13 : b 13 = b 11 * b 12 := hbn 11
  simp [h11, h12] at h13
  have h14 : b 14 = b 12 * b 13 := hbn 12
  simp [h12, h13] at h14
  have h15 : b 15 = b 13 * b 14 := hbn 13
  simp [h13, h14] at h15
  have h16 : b 16 = b 14 * b 15 := hbn 14
  simp [h14, h15] at h16
  have h17 : b 17 = b 15 * b 16 := hbn 15
  simp [h15, h16] at h17
  have h18 : b 18 = b 16 * b 17 := hbn 16
  simp [h16, h17] at h18
  have h19 : b 19 = b 17 * b 18 := hbn 17
  calc 
    b 19 = b 17 * b 18 := h19
    _ = 2 ^ 4181 := by 
      simp [h17, h18]
      <;> norm_num
      <;> try { tauto }