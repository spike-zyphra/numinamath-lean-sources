import Mathlib

theorem algebra_221566 {x y z : ℝ} (h : x ≠ y ∧ y ≠ z ∧ z ≠ x) (h1 : x / (y - z) + y / (z - x) + z / (x - y) = 0) :
    x / (y - z) ^ 2 + y / (z - x) ^ 2 + z / (x - y) ^ 2 = 0 := by 
  have hx1 : x ≠ y := h.1
  have hy1 : y ≠ z := h.2.1
  have hz1 : z ≠ x := h.2.2
  have h2 : y - z ≠ 0 := by 
    intro h'
    apply hy1
    linarith
  have h3 : z - x ≠ 0 := by
    intro h'
    apply hz1
    linarith
  have h4 : x - y ≠ 0 := by
    intro h'
    apply hx1
    linarith
  have eq1 : x / (y - z) ^ 2 + y / (z - x) ^ 2 + z / (x - y) ^ 2 =
      (x / (y - z) + y / (z - x) + z / (x - y)) * (1 / (y - z) + 1 / (z - x) + 1 / (x - y)) := by
    field_simp [(show y - z ≠ 0 by assumption), (show z - x ≠ 0 by assumption), (show x - y ≠ 0 by assumption)]
    <;> ring
  rw [eq1]
  rw [h1]
  all_goals norm_num