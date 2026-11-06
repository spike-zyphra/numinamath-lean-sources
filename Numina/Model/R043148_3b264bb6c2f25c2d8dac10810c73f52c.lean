import Mathlib

theorem algebra_304706 {x y z a b c : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : y / x + x / z = a) (h2 : z / y + y / x = b) (h3 : x / z + z / y = c) :
    (b + c - a) * (c + a - b) * (a + b - c) = 8 := by
  have eq1 : a * x * z = y * z + x ^ 2 := by
    have eq1' : y / x + x / z = a := h1
    field_simp [hx, hz] at eq1' ⊢
    linarith [eq1']
  have eq2 : b * x * y = z * x + y ^ 2 := by
    have eq2' : z / y + y / x = b := h2
    field_simp [hx, hy] at eq2' ⊢
    linarith [eq2']
  have eq3 : c * y * z = x * y + z ^ 2 := by
    have eq3' : x / z + z / y = c := h3
    field_simp [hz, hy] at eq3' ⊢
    linarith [eq3']
  have eq4 : b + c - a = 2 * (z / y) := by
    have eq1' : a = y / x + x / z := by linarith
    have eq2' : b = z / y + y / x := by linarith
    have eq3' : c = x / z + z / y := by linarith
    rw [eq1', eq2', eq3']
    field_simp [hx, hy, hz]
    <;> ring
  have eq5 : c + a - b = 2 * (x / z) := by
    have eq1' : a = y / x + x / z := by linarith
    have eq2' : b = z / y + y / x := by linarith
    have eq3' : c = x / z + z / y := by linarith
    rw [eq1', eq2', eq3']
    field_simp [hx, hy, hz]
    <;> ring
  have eq6 : a + b - c = 2 * (y / x) := by
    have eq1' : a = y / x + x / z := by linarith
    have eq2' : b = z / y + y / x := by linarith
    have eq3' : c = x / z + z / y := by linarith
    rw [eq1', eq2', eq3']
    field_simp [hx, hy, hz]
    <;> ring
  calc 
    (b + c - a) * (c + a - b) * (a + b - c)
      = (2 * (z / y)) * (2 * (x / z)) * (2 * (y / x)) := by rw [eq4, eq5, eq6]
    _ = 8 * ((z / y) * (x / z) * (y / x)) := by ring
    _ = 8 * 1 := by
      have h5 : (z / y) * (x / z) * (y / x) = 1 := by
        field_simp [hy, hz, hx]
        <;> ring
      rw [h5]
    _ = 8 := by ring