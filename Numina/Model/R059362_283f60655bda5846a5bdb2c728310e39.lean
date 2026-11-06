import Mathlib

theorem algebra_145118 (x : ℝ) (hx : x < -2) : (x^2 - 1 + abs (x + 1)) / (x^2 - 2 * x) = (x + 1) / x := by
  have h1 : abs (x + 1) = -(x + 1) := by
    rw [abs_of_neg]
    linarith
  have h2 : x^2 - 2 * x ≠ 0 := by
    by_contra h
    have h3 : x * (x - 2) = 0 := by linarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · linarith
    · linarith
  have hx5 : x ≠ 0 := by
    by_contra h
    linarith
  have h3 : x^2 - 1 + abs (x + 1) = (x + 1) * (x - 2) := by
    rw [h1]
    ring
  have h4 : (x ^ 2 - 2 * x) = x * (x - 2) := by
    ring
  rw [h3, h4]
  have h5 : x - 2 ≠ 0 := by
    by_contra h
    have h6 : x = 2 := by linarith
    linarith
  field_simp [hx5, h5]
  <;> ring_nf <;> field_simp [hx5, h5] <;> ring