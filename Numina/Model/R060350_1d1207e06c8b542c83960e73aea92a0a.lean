import Mathlib

theorem algebra_174829 (v : ℝ) (h : v > 0) (h1 : 1 / v + 25 / v + 4 / v = 1.25)
    (h2 : 1 / (16 * v) + 25 / (49 * v) + 4 / (49 * v) = 5 / 4) :
    25 / v = 5 / 7 := by
  have eq1 : 30 / v = 1.25 := by
    calc
      30 / v = (1 / v + 25 / v + 4 / v) := by field_simp <;> ring
      _ = 1.25 := h1

  have hv : v = (30 : ℝ) / 1.25 := by
    field_simp at eq1 ⊢
    all_goals
      nlinarith

  rw [hv] at h2
  norm_num at h2 ⊢
  all_goals
    linarith