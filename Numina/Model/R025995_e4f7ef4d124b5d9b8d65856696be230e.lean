import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_12728 {a : ℝ} (ha : 0 < a ∧ a ≠ 1)
  (A : ℝ × ℝ) (hA : A.1 = -3 ∧ A.2 = a ^ 0 - 2)
  (m n : ℝ) (hm : 0 < m) (hn : 0 < n)
  (hA' : A.1 / m + A.2 / n + 1 = 0) :
  3 * m + n ≥ 16 := by
  rcases hA with ⟨hx, hy⟩
  have h1 : A.1 / m + A.2 / n + 1 = 0 := hA'
  rw [hx] at h1
  have h2 : a ^ 0 = 1 := by simp
  have h3 : A.2 = -1 := by
    rw [hy]
    rw [h2]
    norm_num
  rw [h3] at h1
  have h5 : 3 / m + 1 / n = 1 := by
    field_simp [(show m ≠ 0 by linarith), (show n ≠ 0 by linarith)] at h1 ⊢
    linarith
  have h6 : m * n = m + 3 * n := by
    field_simp [(show m ≠ 0 by linarith), (show n ≠ 0 by linarith)] at h5
    nlinarith
  nlinarith [sq_nonneg (m - 4), sq_nonneg (n - 4),
    mul_pos hm hn, h6, mul_pos (show 0 < m by linarith) (show 0 < n by linarith)]