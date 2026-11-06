import Mathlib

theorem algebra_8109 {x y : ℝ} (h : y ≠ 0) (h' : x ≠ 0) (h'' : y / x - 5 * y = 1) :
    (2 * x - 3 * x * y - 2 * y) / (x - 2 * x * y - y) = 13 / 7 := by

  have eq1 : y - x - 5 * x * y = 0 := by 
    have eq6 : y / x - 5 * y = 1 := h''
    have eq9 : (y / x - 5 * y) * x = 1 * x := by
      rw [h'']
    have eq14 : (y / x - 5 * y) * x = y - 5 * x * y := by
      field_simp [h']
      <;> ring
    have eq15 : (1 * x) = x := by ring
    have eq7 : y - 5 * x * y = x := by
      linarith [eq9, eq14, eq15]
    linarith [eq7]

  have eq2 : x - y = -5 * x * y := by
    linarith [eq1]

  have eq3 : 2 * x - 3 * x * y - 2 * y = -13 * (x * y) := by
    have eq4 : x - y = -5 * x * y := eq2
    have eq5 : 2 * x - 3 * x * y - 2 * y = 2 * (x - y) - 3 * x * y := by ring
    rw [eq5]
    rw [show x - y = -5 * x * y by linarith [eq2]]
    ring

  have eq4 : x - 2 * x * y - y = -7 * (x * y) := by
    have eq5 : x - y = -5 * x * y := eq2
    have eq6 : x - 2 * x * y - y = (x - y) - 2 * x * y := by ring
    rw [eq6]
    rw [show x - y = -5 * x * y by linarith [eq2]]
    ring

  have eq5 : x * y ≠ 0 := by
    apply mul_ne_zero
    exact h'
    exact h

  have eq6 : (2 * x - 3 * x * y - 2 * y) / (x - 2 * x * y - y) = 13 / 7 := by
    rw [eq3, eq4]
    have eq7 : x * y ≠ 0 := eq5
    field_simp [show x * y ≠ 0 by exact eq5]
    <;> nlinarith

  exact eq6