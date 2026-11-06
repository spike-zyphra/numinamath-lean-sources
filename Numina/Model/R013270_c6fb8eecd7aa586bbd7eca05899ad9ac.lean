import Mathlib

theorem algebra_173690 {a1 b1 : ℝ} (ha : 0 < a1) (hb : 0 < b1) :
    (a1 * b1 - (a1 * (1 - 25 / 100) * b1 * (1 + 20 / 100))) / (a1 * b1) = 10 / 100 := by
  have h1 : a1 * b1 > 0 := by
    apply mul_pos
    exact ha
    exact hb
  have eq1 : a1 * b1 - (a1 * (1 - 25 / 100) * b1 * (1 + 20 / 100)) = a1 * b1 * (10 / 100) := by
    ring_nf
  rw [eq1]
  have h2 : a1 * b1 ≠ 0 := by
    positivity
  field_simp [h2]
  <;> ring_nf