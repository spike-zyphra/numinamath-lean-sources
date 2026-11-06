import Mathlib

theorem algebra_7787
(x y z : ℝ)
(h₀ : 0 < x)
(h₁ : 0 < y)
(h₂ : 0 < z)
(h₃ : x + 2 * y + z = 5 * (x + y) * (y + z))
(h₄ : y + 2 * z + x = 7 * (y + z) * (z + x))
(h₅ : z + 2 * x + y = 6 * (z + x) * (x + y)) :
x * y * z = 35 / 13824 := by

  have eq1 : (x + y) + (y + z) = 5 * (x + y) * (y + z) := by
    linarith
  have eq2 : (y + z) + (z + x) = 7 * (y + z) * (z + x) := by
    linarith
  have eq3 : (z + x) + (x + y) = 6 * (z + x) * (x + y) := by
    linarith

  have h6 : x + y > 0 := by
    nlinarith
  have h7 : y + z > 0 := by
    nlinarith
  have h8 : z + x > 0 := by
    nlinarith

  have eq4 : 1 / (x + y) + 1 / (y + z) = 5 := by
    have hne1 : x + y ≠ 0 := by linarith
    have hne2 : y + z ≠ 0 := by linarith
    field_simp at eq1 ⊢
    linarith

  have eq5 : 1 / (y + z) + 1 / (z + x) = 7 := by
    have hne1 : y + z ≠ 0 := by linarith
    have hne2 : z + x ≠ 0 := by linarith
    field_simp at eq2 ⊢
    linarith

  have eq6 : 1 / (z + x) + 1 / (x + y) = 6 := by
    have hne1 : z + x ≠ 0 := by linarith
    have hne2 : x + y ≠ 0 := by linarith
    field_simp at eq3 ⊢
    linarith

  have eq7 : 1 / (x + y) = 2 := by
    linarith [eq4, eq5, eq6]

  have eq8 : 1 / (y + z) = 3 := by
    linarith [eq4, eq5, eq6]

  have eq9 : 1 / (z + x) = 4 := by
    linarith [eq4, eq5, eq6]

  have eq10 : x + y = 1 / 2 := by
    have hne1 : x + y ≠ 0 := by linarith
    field_simp at eq7 ⊢
    linarith

  have eq11 : y + z = 1 / 3 := by
    have hne1 : y + z ≠ 0 := by linarith
    field_simp at eq8 ⊢
    linarith

  have eq12 : z + x = 1 / 4 := by
    have hne1 : z + x ≠ 0 := by linarith
    field_simp at eq9 ⊢
    linarith

  have eq13 : x = 5 / 24 := by
    nlinarith [eq10, eq11, eq12]

  have eq14 : y = 7 / 24 := by
    nlinarith [eq10, eq11, eq12, eq13]

  have eq15 : z = 1 / 24 := by
    nlinarith [eq11, eq12, eq13, eq14]

  rw [eq13, eq14, eq15]
  norm_num