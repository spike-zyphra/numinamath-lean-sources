import Mathlib

theorem algebra_318837 {a b c : ℝ} (h : a ≠ 0) (h1 : (1 / 4) * (b - c) ^ 2 = (a - b) * (c - a)) :
    (b + c) / a = 2 := by
  have h2 : (b - c) ^ 2 = 4 * (a - b) * (c - a) := by
    linarith [h1]

  have h3 : (b + c - 2 * a) ^ 2 = 0 := by
    nlinarith [sq_nonneg (b - a), sq_nonneg (c - a), sq_nonneg (b + c - 2 * a), sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]

  have h4 : b + c - 2 * a = 0 := by
    rw [sq_eq_zero_iff] at h3
    exact h3

  have h5 : b + c = 2 * a := by linarith

  have h6 : (b + c) / a = 2 := by
    rw [h5]
    field_simp [h]
    <;> ring_nf
    <;> field_simp [h]

  exact h6