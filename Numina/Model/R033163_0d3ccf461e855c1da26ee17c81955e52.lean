import Mathlib

theorem algebra_313163 {a b : ℝ} (ha : a ≥ 1) (hb : b ≥ 1)
    (h : Real.sqrt (a - 1) + (a * b - 2) ^ 2 = 0) :
    ∑ i ∈ Finset.range 1991, (1 / ((a + i) * (b + i))) = 1991 / 1992 := by
  have h1 : Real.sqrt (a - 1) ≥ 0 := by
    apply Real.sqrt_nonneg
  have h2 : (a * b - 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h3 : Real.sqrt (a - 1) = 0 := by
    linarith
  have h4 : (a * b - 2) ^ 2 = 0 := by
    linarith
  have h5 : a - 1 = 0 := by
    rw [Real.sqrt_eq_zero (by linarith)] at h3
    linarith
  have ha1 : a = 1 := by
    linarith
  have h6 : a * b - 2 = 0 := by
    rw [sq_eq_zero_iff] at h4
    linarith
  have h7 : a * b = 2 := by
    linarith
  have hb1 : b = 2 := by
    rw [ha1] at h7
    linarith
  rw [ha1, hb1]
  norm_num
  <;> native_decide