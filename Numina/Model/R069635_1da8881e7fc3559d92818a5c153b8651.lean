import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_226062 {a : ℝ} (ha : 0 < a ∧ a ≠ 1)
  (A : ℝ × ℝ) (hA : A.1 = -3 ∧ A.2 = a^0 - 2)
  (m n : ℝ) (hm : 0 < m) (hn : 0 < n)
  (hmn : A.1 / m + A.2 / n + 1 = 0) :
  3 * m + n ≥ 16 := by
  have hA1 : A.1 = -3 := by 
    exact hA.1
  have hA2 : A.2 = -1 := by
    have h1 : A.2 = a^0 - 2 := hA.2
    rw [h1]
    norm_num
  rw [hA1, hA2] at hmn
  have h1 : 3 / m + 1 / n = 1 := by 
    field_simp at hmn ⊢
    nlinarith 
  have h2 : 3 * m + n ≥ 16 := by
    have h3 : m > 0 := hm
    have h4 : n > 0 := hn
    have h5 : 3 / m + 1 / n = 1 := h1
    have h6 : m * n - m - 3 * n = 0 := by 
      field_simp at h5 
      nlinarith 
    nlinarith [sq_nonneg (m - 4), sq_nonneg (n - 4),
      mul_pos hm hn]
  linarith [h2]