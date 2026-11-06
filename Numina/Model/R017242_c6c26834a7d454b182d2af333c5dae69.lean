import Mathlib

theorem algebra_312054 {a b c : ℝ} (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0)
    (h''' : a + b + c = 0) :
    a * (1 / b + 1 / c) + b * (1 / a + 1 / c) + c * (1 / a + 1 / b) = -3 := by
  have eq1 : a * (1 / b + 1 / c) + b * (1 / a + 1 / c) + c * (1 / a + 1 / b) =
    (a^2 * c + a^2 * b + b^2 * a + b^2 * c + c^2 * a + c^2 * b) / (a * b * c) := by
    field_simp [h, h', h'']
    ring
  have eq2 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact h
    exact h'
    exact h''
  rw [eq1]
  have eq3 : a^2 * c + a^2 * b + b^2 * a + b^2 * c + c^2 * a + c^2 * b = -3 * (a * b * c) := by
    have h1 : c = -a - b := by linarith
    rw [h1]
    ring_nf
    <;> nlinarith [sq_pos_of_ne_zero h, sq_pos_of_ne_zero h', sq_pos_of_ne_zero h'']
  rw [eq3]
  field_simp [eq2]
  <;> nlinarith