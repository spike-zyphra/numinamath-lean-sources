import Mathlib

theorem algebra_12778 {a b c p : ℝ} (ha : a ≠ 0) (hp : p ≠ 0)
    (h₁ : ∀ x, a * x ^ 2 + b * x + c = a * (x - p) ^ 2 + p) (h₂ : c = -p) :
    b = 4 := by
  have eq1 := h₁ 0
  simp at eq1
  rw [h₂] at eq1
  have eq2 : a * p ^ 2 + 2 * p = 0 := by
    nlinarith
  have eq3 : a * p + 2 = 0 := by
    apply (mul_left_inj' hp).mp
    linarith
  have eq4 : a * p = -2 := by
    linarith
  have eq7 : b = -2 * a * p := by
    have eq8 := h₁ 1
    have eq9 := h₁ 0
    have eq10 := h₁ 2
    norm_num at eq8 eq9 eq10 
    nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hp]
  rw [eq7]
  have eq12 : -2 * a * p = 4 := by
    have eq13 : a * p = -2 := eq4
    have : -2 * a * p = -2 * (a * p ) := by ring
    rw [this, eq13]
    all_goals linarith
  linarith [eq12]