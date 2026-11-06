import Mathlib

theorem algebra_204210 (x : ℝ) (hx : x ≠ 0) (h : (2 * x - 3) ^ 2 = (x / 2) * (18 / x + 1)) :
    (2 * x - 3) / (x / 2) = 2.08 := by
  have h1 : (x / 2) * (18 / x + 1) = 9 + x / 2 := by
    field_simp [hx]
    ring
  rw [h1] at h
  have h2 : (2 * x - 3) ^ 2 = 4 * x ^ 2 - 12 * x + 9 := by ring
  rw [h2] at h
  have h3 : 4 * x ^ 2 - 25 / 2 * x = 0 := by linarith
  have h4 : x * (8 * x - 25) = 0 := by
    linarith
  have hx2 : x = 25 / 8 := by
    cases (mul_eq_zero.mp h4) with
    | inl h5 => 
      exfalso
      exact hx (by linarith)
    | inr h6 =>
      linarith
  rw [hx2]
  norm_num