import Mathlib

theorem algebra_204210 (x : ℝ) (hx : x ≠ 0) (h : (2 * x - 3) ^ 2 = (x / 2) * (18 / x + 1)) :
    (2 * x - 3) / (x / 2) = 2.08 := by
  have eq1 : (2 * x - 3) ^ 2 = 9 + x / 2 := by
    have h1 : (x / 2) * (18 / x + 1) = 9 + x / 2 := by
      field_simp [hx]
      <;> ring
    linarith [h, h1]
  have h2 : (2 * x - 3) ^ 2 = 4 * x ^ 2 - 12 * x + 9 := by ring
  rw [h2] at eq1
  have h3 : 4 * x ^ 2 - 12 * x = x / 2 := by linarith
  have h4 : 8 * x ^ 2 - 25 * x = 0 := by
    linarith
  have h5 : x * (8 * x - 25) = 0 := by
    linarith
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- x = 0 is a contradiction
    exfalso
    exact hx (by linarith)
  · -- 8 * x - 25 = 0, so x = 25 / 8
    have hx2 : x = 25 / 8 := by linarith
    rw [hx2]
    norm_num
    <;> linarith