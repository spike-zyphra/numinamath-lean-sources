import Mathlib

theorem inequalities_115728 (x y z : ℤ) : x^2 + y^2 + z^2 + 3 < x * y + 3 * y + 2 * z ↔ (x, y, z) = (1, 2, 1) := by
  constructor
  · -- Assume the inequality holds, prove (x, y, z) = (1, 2, 1)
    rintro h
    have h1 : (2 * x - y : ℤ)^2 + 3 * (y - 2 : ℤ) ^ 2 + 4 * (z - 1 : ℤ) ^ 2 < 4 := by
      nlinarith
    have h4 : z = 1 := by
      nlinarith [sq_nonneg ((2 * x - y : ℤ)), sq_nonneg ((y - 2 : ℤ)), sq_nonneg ((z - 1 : ℤ)), sq_nonneg ((2 * x - y : ℤ)), sq_nonneg ((y - 2 : ℤ)), sq_nonneg ((z - 1 : ℤ)), sq_nonneg ((y - 2 : ℤ)), sq_nonneg ((2 * x - y : ℤ))]
    rw [h4] at h1
    have h8 : y = 2 := by
      nlinarith [sq_nonneg ((2 * x - y : ℤ)), sq_nonneg ((y - 2 : ℤ)), sq_nonneg ((z - 1 : ℤ)), sq_nonneg ((2 * x - y : ℤ)), sq_nonneg ((y - 2 : ℤ)), sq_nonneg ((z - 1 : ℤ))]
    have h9 : x = 1 := by
      nlinarith [sq_nonneg ((x - 1 : ℤ)), sq_nonneg ((y - 2 : ℤ)), sq_nonneg ((2 * x - y : ℤ)), h8]
    simp [Prod.ext_iff, h9, h8, h4]
  · -- Show the inequality holds for (1, 2, 1)
    rintro ⟨rfl, rfl, rfl⟩
    norm_num