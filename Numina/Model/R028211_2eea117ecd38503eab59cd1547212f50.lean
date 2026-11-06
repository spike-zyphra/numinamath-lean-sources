import Mathlib

theorem algebra_149738 {x y z : ℝ} (h : x ≠ 0) (h' : y ≠ 0) (h'' : z ≠ 0)
    (h''' : x / y + y / z + z / x = z / y + y / x + x / z) :
    x = y ∨ y = z ∨ x = z := by
  have eq1 : x ^ 2 * z + x * y ^ 2 + y * z ^ 2 - (x * z ^ 2 + y ^ 2 * z + x ^ 2 * y) = 0 := by
    have eq2 : x / y + y / z + z / x - (z / y + y / x + x / z) = 0 := by
      linarith
    have eq3 : (x / y + y / z + z / x - (z / y + y / x + x / z)) * (x * y * z) = 0 := by
      rw [eq2]
      norm_num
    have eq4 : x ^ 2 * z + x * y ^ 2 + y * z ^ 2 - (x * z ^ 2 + y ^ 2 * z + x ^ 2 * y) = 0 := by
      have eq5 : (x / y + y / z + z / x - (z / y + y / x + x / z)) * (x * y * z) =
        x ^ 2 * z + x * y ^ 2 + y * z ^ 2 - (x * z ^ 2 + y ^ 2 * z + x ^ 2 * y) := by
        field_simp [h, h', h'']
        <;> ring
      linarith [eq3, eq5]
    linarith
  have eqn2 : (x - y) * (x - z) * (y - z) = 0 := by
    nlinarith [eq1]
  cases' (mul_eq_zero.mp eqn2) with eqn3 eqn4
  · cases' (mul_eq_zero.mp eqn3) with eqn5 eqn6
    · -- Case where $x - y = 0$ (so $x = y$)
      left
      linarith
    · -- Case where $x - z = 0$ (so $x = z$)
      right
      right
      linarith
  · -- Case where $y - z = 0$ (so $y = z$)
    right
    left
    linarith