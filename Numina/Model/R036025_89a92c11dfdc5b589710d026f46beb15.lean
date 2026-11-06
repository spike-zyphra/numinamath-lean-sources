import Mathlib

theorem algebra_235078 :
    {(x, y, z) : ℝ × ℝ × ℝ | x - y ≥ z ∧ x ^ 2 + 4 * y ^ 2 + 5 = 4 * z} = {(2, -0.5, 2.5)} := by
  ext ⟨x, y, z⟩
  simp
  constructor
  · -- Assume h : x - y ≥ z ∧ x ^ 2 + 4 * y ^ 2 + 5 = 4 * z
    rintro ⟨h1, h2⟩
    have h3 : z = (x ^ 2 + 4 * y ^ 2 + 5) / 4 := by
      linarith
    rw [h3] at h1
    have h4 : (x - 2) ^ 2 + 4 * (y + 0.5) ^ 2 ≤ 0 := by
      nlinarith
    have hx1 : (x - 2) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 0.5), sq_nonneg (x - 2 * (y + 0.5)), sq_nonneg ((x - 2) - 2 * (y + 0.5))]
    have hy1 : (y + 0.5) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y + 0.5), sq_nonneg (x - 2 * (y + 0.5)), sq_nonneg ((x - 2) - 2 * (y + 0.5))]
    have hx2 : x = 2 := by
      nlinarith
    have hy2 : y = -0.5 := by
      nlinarith
    have hz1 : z = 2.5 := by
      rw [hx2, hy2] at h3
      norm_num at h3 ⊢
      linarith
    simp [hx2, hy2, hz1]
  · -- Show that (2, -0.5, 2.5) satisfy both constraints
    rintro ⟨rfl, rfl, rfl⟩
    constructor
    · norm_num
    · norm_num