import Mathlib

theorem algebra_147824 (x y z : ℝ)
    (h1 : 2*x+3*y-2*z+6=0) (h2 : x-3*y+z+3=0) :
    (x+3)/(-3)=y/(-4) ∧ y/(-4)=z/(-9) := by
  constructor
  · -- Show that (x + 3) / (-3) = y / (-4)
    have h3 : 9 * y = 4 * z := by
      have eq1 : 2 * x + 3 * y - 2 * z + 6 = 0 := h1
      have eq2 : x - 3 * y + z + 3 = 0 := h2
      have eq3 : x = 3 * y - z - 3 := by linarith
      rw [eq3] at eq1
      linarith
    have h4 : y = (4 / 9) * z := by
      linarith
    have h5 : z = 3 * (x + 3) := by
      have eq1 : x - 3 * y + z + 3 = 0 := h2
      rw [show y = (4 / 9) * z by linarith [h4]] at eq1
      linarith
    have h6 : (x + 3) / (-3) = y / (-4) := by
      rw [show y = (4 / 9) * z by linarith [h4]]
      have h7 : z = 3 * (x + 3) := h5
      rw [h7]
      ring_nf
    exact h6
  · -- Show that y / (-4) = z / (-9)
    have h3 : 9 * y = 4 * z := by
      have eq1 : 2 * x + 3 * y - 2 * z + 6 = 0 := h1
      have eq2 : x - 3 * y + z + 3 = 0 := h2
      have eq3 : x = 3 * y - z - 3 := by linarith
      rw [eq3] at eq1
      linarith
    have h8 : 9 * y = 4 * z := by linarith
    have h9 : y = (4 / 9) * z := by
      linarith
    have h10 : y / (-4) = z / (-9) := by
      rw [show y = (4 / 9) * z by linarith [h9]]
      field_simp
      <;> nlinarith
    exact h10