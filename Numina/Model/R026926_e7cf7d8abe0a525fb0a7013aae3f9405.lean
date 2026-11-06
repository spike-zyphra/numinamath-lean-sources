import Mathlib

theorem algebra_135465 (x y z : ℝ) (h1 : 2*x-3*y-2*z+6=0) (h2 : x-3*y+z+3=0) :
    (x+3)/9=y/4 ∧ y/4=z/3 := by
  have h3 : x = 3 * z - 3 := by
    linarith
  have h4 : y = 4 / 3 * z := by
    rw [h3] at h2
    linarith

  constructor
  · -- Prove (x + 3) / 9 = y / 4
    have eq1 : x + 3 = 3 * z := by
      linarith [h3]
    have eq2 : y = 4 / 3 * z := h4
    rw [eq1]
    rw [eq2]
    field_simp
    <;> ring_nf <;> field_simp
  · -- Prove y / 4 = z / 3
    have eq2 : y = 4 / 3 * z := h4
    rw [eq2]
    field_simp
    <;> ring_nf <;> field_simp