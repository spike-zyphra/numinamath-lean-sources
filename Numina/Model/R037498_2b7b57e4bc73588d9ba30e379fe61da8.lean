import Mathlib

theorem algebra_263374 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxyz : x ≠ y ∧ y ≠ z ∧ x ≠ z) (h1 : y / (x - z) = (x + y) / z) (h2 : (x + y) / z = x / y) :
    x / y = 2 := by
  rcases hxyz with ⟨hx1, hyz, h1xz⟩
  have hne1 : x - z ≠ 0 := by
    intro h
    apply h1xz
    linarith
  have hne2 : z ≠ 0 := by nlinarith
  have hne3 : y ≠ 0 := by nlinarith
  have eq1 : y * z = (x + y) * (x - z) := by
    have h3 : x - z ≠ 0 := hne1
    have hne2z : z ≠ 0 := hne2
    field_simp [h3, hne2z] at h1
    nlinarith
  have eq2 : (x + y) * y = x * z := by
    have hne2z : z ≠ 0 := hne2
    have hne3y : y ≠ 0 := hne3
    field_simp [hne2z, hne3y] at h2
    nlinarith
  have eq3 : x^2 - x * y - 2 * y^2 = 0 := by
    have eq1' : y * z = (x + y) * (x - z) := eq1
    have eq2' : (x + y) * y = x * z := eq2
    nlinarith [sq_nonneg (x - 2 * y), sq_nonneg (y), sq_pos_of_pos hy, sq_pos_of_pos hx]
  have h4 : x = 2 * y := by
    have h : (x - 2 * y) * (x + y) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h) with h6 h7
    · linarith
    · nlinarith
  have hfrac : x / y = 2 := by
    field_simp [show y ≠ 0 by linarith]
    linarith [h4]
  exact hfrac