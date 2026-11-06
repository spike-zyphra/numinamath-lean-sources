import Mathlib

theorem algebra_297143 {r h : ℝ} (hr : r > 0) (hh : h > 0)
    (hvol : π * r^2 * h = 2) (hsurf : 2 * π * r * (r + h) = 24) :
    1 / r + 1 / h = 6 := by

  have eq1 : π * r * (r + h) = 12 := by
    nlinarith

  have h3 : r + h = 6 * r * h := by
    have eq2 : r ^ 2 * h * π = 2 := by
      nlinarith
    have eq3 : r * (r + h) * π = 12 := by
      nlinarith
    have eq5 : π = 2 / (r ^ 2 * h) := by
      have hne : r ^ 2 * h ≠ 0 := by positivity
      field_simp [hne]
      nlinarith
    have eq6 : π = 12 / (r * (r + h)) := by
      have hne : r * (r + h) ≠ 0 := by
        apply mul_ne_zero
        linarith
        linarith
      field_simp [hne]
      nlinarith
    have eq8 : 2 * r * (r + h) = 12 * r ^ 2 * h := by
      rw [eq5] at eq6
      field_simp [(show r^2 * h ≠ 0 by positivity), (show r * (r + h) ≠ 0 by
        apply mul_ne_zero
        linarith
        linarith
      )] at eq6 ⊢
      nlinarith [sq_nonneg (r), sq_nonneg (h), mul_pos hr hh]
    have eq9 : r + h = 6 * r * h := by
      apply (mul_left_inj' (show (2 * r) ≠ 0 by positivity)).mp
      linarith [eq8]
    nlinarith

  have eq10 : 1 / r + 1 / h = (r + h) / (r * h) := by
    field_simp [show r ≠ 0 by linarith, show h ≠ 0 by linarith]
    <;> ring_nf

  rw [eq10]
  have eq11 : (r + h) / (r * h) = 6 := by
    have eq12 : r + h = 6 * r * h := by
      linarith [h3]
    have hne : r * h ≠ 0 := by
      positivity
    field_simp [hne]
    nlinarith

  exact_mod_cast eq11