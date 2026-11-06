import Mathlib

theorem algebra_198059 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : x * y = 1) (hxi : (x * 1.1) * y * (1 - d / 100) = 1) :
    d = 100 / 11 := by
  have hy_eq : y = 1 / x := by
    field_simp [(show x ≠ 0 by linarith)]
    nlinarith
  rw [hy_eq] at hxi
  have hx1 : x ≠ 0 := by linarith
  have eq1 : (x * 1.1) * (1 / x) * (1 - d / 100) = 1.1 * (1 - d / 100) := by
    field_simp [hx1]
    <;> ring_nf
  rw [eq1] at hxi
  ring_nf at hxi
  field_simp [(show (11 : ℝ) ≠ 0 by norm_num)] at hxi ⊢
  nlinarith