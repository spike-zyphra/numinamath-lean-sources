import Mathlib

theorem algebra_320676 {a b c x : ℝ} (h : a ≠ 0) (h' : b ≠ 0) (h'' : c ≠ 0)
    (h''' : a + b + c ≠ 0) (h'''' : (x - a) / (b * c) + (x - b) / (a * c) + (x - c) / (a * b) =
    2 * (1 / a + 1 / b + 1 / c)) : x = a + b + c := by

  have eq1 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact h
    exact h'
    exact h''
  have eq2 : a * b * c * ((x - a) / (b * c) + (x - b) / (a * c) + (x - c) / (a * b)) =
          a * b * c * (2 * (1 / a + 1 / b + 1 / c)) := by
    rw [h'''']
  have eq3 : a * b * c * ((x - a) / (b * c) + (x - b) / (a * c) + (x - c) / (a * b)) =
          a * (x - a) + b * (x - b) + c * (x - c) := by
    have h1 : a * b * c * ((x - a) / (b * c) + (x - b) / (a * c) + (x - c) / (a * b)) =
          a * b * c * ((x - a) / (b * c)) + a * b * c * ((x - b) / (a * c)) + a * b * c * ((x - c) / (a * b)) := by ring
    rw [h1]
    have h2 : a * b * c * ((x - a) / (b * c)) = a * (x - a) := by
      field_simp [h', h'']
      <;> ring
    have h3 : a * b * c * ((x - b) / (a * c)) = b * (x - b) := by
      field_simp [h, h'']
      <;> ring
    have h4 : a * b * c * ((x - c) / (a * b)) = c * (x - c) := by
      field_simp [h, h']
      <;> ring
    rw [h2, h3, h4]
  have eq4 : a * b * c * (2 * (1 / a + 1 / b + 1 / c)) =
          2 * (b * c + a * c + a * b) := by
    field_simp [h, h', h'']
    <;> ring
  rw [eq3, eq4] at eq2
  have eq5 : a * (x - a) + b * (x - b) + c * (x - c) = 2 * (b * c + a * c + a * b) := by linarith
  have eq6 : x * (a + b + c) - (a + b + c) ^ 2 = 0 := by
    linarith [eq5]
  have eq7 : (x - (a + b + c)) * (a + b + c) = 0 := by
    linarith [eq6]
  cases' (mul_eq_zero.mp eq7) with h8 h9
  · -- x - (a + b + c) = 0
    linarith
  · -- a + b + c = 0
    exfalso
    apply h'''
    linarith