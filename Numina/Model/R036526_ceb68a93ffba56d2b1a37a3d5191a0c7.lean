import Mathlib

theorem algebra_8047 {x t : ℝ} (ht : t ≠ 0) (h : x + 1 / (9 * x - 6) = (t ^ 2 + 2 * t + 1) / (3 * t)) :
    x = (2 + t) / 3 ∨ x = (1 + 2 * t) / (3 * t) := by

  have h1 : 9 * x - 6 ≠ 0 := by
    by_contra h1
    have h1 : x = 2 / 3 := by linarith
    rw [h1] at h
    field_simp [ht] at h
    <;> nlinarith
  have eq1 : (x * (9 * x - 6) + 1) * (3 * t) = (t ^ 2 + 2 * t + 1) * (9 * x - 6) := by
    have eq1 : 9 * x - 6 ≠ 0 := h1
    have ht1 : t ≠ 0 := ht
    field_simp [ht1, eq1] at h ⊢
    nlinarith [sq_pos_of_ne_zero ht1, sq_nonneg (9 * x - 6), sq_nonneg (x - 2 / 3)]
  have eq2 : (x - (2 + t) / 3) * (x - (1 + 2 * t) / (3 * t)) = 0 := by
    field_simp [ht] at eq1 ⊢
    nlinarith [sq_pos_of_ne_zero ht, sq_nonneg (x * t - (2 + t) / 3 * t), sq_nonneg (x - (2 + t) / 3), sq_nonneg (x - (1 + 2 * t) / (3 * t)), sq_pos_of_ne_zero ht]
  cases (mul_eq_zero.mp eq2) with
  | inl h2 =>
    left
    linarith
  | inr h3 =>
    right
    field_simp [ht] at h3 ⊢
    linarith