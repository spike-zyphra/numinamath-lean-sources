import Mathlib

theorem algebra_160223 (x y : ℝ) (hxy : x^2 * y = 3 ∧ x + x * y = 4) :
    (x, y) = (1, 3) ∨ (x, y) = (3, 1 / 3) := by
  rcases hxy with ⟨h1, h2⟩
  have eq1 : x ≠ 0 := by
    by_contra h
    have h3 : x = 0 := by linarith
    rw [h3] at h1 h2
    nlinarith
  have eq2 : y = 4 / x - 1 := by
    have h3 : x ≠ 0 := eq1
    field_simp [h3]
    nlinarith [h2]
  rw [eq2] at h1
  have eq3 : x ^ 2 - 4 * x + 3 = 0 := by
    have h3 : x ≠ 0 := eq1
    have eq4 : x ^ 2 * (4 / x - 1) = 4 * x - x ^ 2 := by
      field_simp [h3]
      <;> ring
    have eq5 : x ^ 2 * (4 / x - 1) = 3 := h1
    nlinarith [eq4, eq5]
  have eq4 : (x - 1) * (x - 3) = 0 := by nlinarith [eq3]
  cases' (mul_eq_zero.mp eq4) with h5 h6
  · -- Case $x - 1 = 0$, so $x = 1$
    have hx1 : x = 1 := by linarith
    have hy1 : y = 3 := by
      rw [hx1] at eq2
      norm_num at eq2 ⊢
      linarith [eq2]
    left
    simp [hx1, hy1]
  · -- Case $x - 3 = 0$, so $x = 3$
    have hx2 : x = 3 := by linarith
    have hy2 : y = 1 / 3 := by
      rw [hx2] at eq2
      norm_num at eq2 ⊢
      linarith [eq2]
    right
    simp [hx2, hy2]