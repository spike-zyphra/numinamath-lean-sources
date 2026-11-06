import Mathlib

theorem algebra_300540 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : 1 / (a - b) + 1 / (b - c) + 1 / (c - a) = 1) :
    (1 / (a - b)^2) + (1 / (b - c)^2) + (1 / (c - a)^2) = 1 := by

  have h1 : a - b ≠ 0 := by
    intro h11
    apply ha
    linarith

  have h2 : b - c ≠ 0 := by
    intro h22
    apply hb
    linarith

  have h3 : c - a ≠ 0 := by
    intro h33
    apply hc
    linarith

  have eq1 : (1 / (a - b)^2) + (1 / (b - c)^2) + (1 / (c - a)^2) =
      (1 / (a - b) + 1 / (b - c) + 1 / (c - a))^2 - 2 * (1 / ((a - b) * (b - c)) + 1 / ((b - c) * (c - a)) + 1 / ((c - a) * (a - b)) ) := by
    field_simp [h1, h2, h3, mul_ne_zero h1 h2, mul_ne_zero h2 h3, mul_ne_zero h3 h1]
    <;> ring

  have eq2 : 1 / ((a - b) * (b - c)) + 1 / ((b - c) * (c - a)) + 1 / ((c - a) * (a - b)) = 0 := by
    field_simp [h1, h2, h3, mul_ne_zero h1 h2, mul_ne_zero h2 h3, mul_ne_zero h3 h1]
    <;> ring

  rw [eq1, h, eq2]
  norm_num