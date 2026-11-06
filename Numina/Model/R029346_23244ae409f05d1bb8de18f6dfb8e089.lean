import Mathlib

theorem algebra_196 (x y z : ℝ) (hx : x ≠ 0) (hy : y + 2 * z ≠ 0) :
    ((5 * y + 10 * z) / x) * (6 * x / (-14 * z - 7 * y)) + 3 * x - 2 = -44 / 7 + 3 * x := by

  have h1 : -14 * z - 7 * y ≠ 0 := by
    intro h
    have h2 : y + 2 * z = 0 := by 
      nlinarith
    contradiction

  have h3 : ((5 * y + 10 * z) / x) * (6 * x / (-14 * z - 7 * y)) = -30 / 7 := by 
    have h2 : (5 * y + 10 * z) = 5 * (y + 2 * z) := by ring
    have h3 : (-14 * z - 7 * y) = -7 * (y + 2 * z) := by ring
    rw [h2, h3]
    have hx2 : x ≠ 0 := hx
    have hy2 : y + 2 * z ≠ 0 := hy
    have hx3 : x ≠ 0 := hx
    field_simp [hx2, hy2, show (-7 : ℝ) ≠ 0 by norm_num]
    <;> ring_nf <;> field_simp
    <;> nlinarith [show y + 2 * z ≠ 0 by exact_mod_cast hy]
  rw [h3]
  linarith