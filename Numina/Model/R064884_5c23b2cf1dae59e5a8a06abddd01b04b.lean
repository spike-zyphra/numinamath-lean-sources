import Mathlib

theorem algebra_168950 {p : ℝ} (hp : p ∈ Set.Icc 0 1) (h : (1 - (1 - p) ^ 3) = 0.973) :
    p = 0.7 := by
  have h1 : (1 - p) ^ 3 = 0.027 := by
    nlinarith
  have h3 : (1 - p - (0.3 : ℝ)) * ((1 - p) ^ 2 + (1 - p) * (0.3 : ℝ) + (0.3 : ℝ) ^ 2) = 0 := by
    have h4 : (1 - p) ^ 3 - (0.3 : ℝ) ^ 3 = 0 := by
      have h5 : (1 - p) ^ 3 = (0.027 : ℝ) := h1
      have h6 : (0.3 : ℝ) ^ 3 = (0.027 : ℝ) := by
        norm_num
      nlinarith
    have h7 : (1 - p) ^ 3 - (0.3 : ℝ) ^ 3 =
      (1 - p - (0.3 : ℝ)) * ((1 - p) ^ 2 + (1 - p) * (0.3 : ℝ) + (0.3 : ℝ) ^ 2) := by
      ring
    rw [h7] at h4
    linarith
  cases' (mul_eq_zero.mp h3) with h6 h7
  · -- Case where (1 - p) - 0.3 = 0
    have hp_eq : p = 0.7 := by
      nlinarith
    exact hp_eq
  · -- Case where (1-p)^2 + (1-p)(0.3) + (0.3)^2 = 0
    have h8 : (1 - p) ^ 2 + (1 - p) * (0.3 : ℝ) + (0.3 : ℝ) ^ 2 > 0 := by
      nlinarith [sq_nonneg ( (1 - p) + (0.3 : ℝ) / 2 ), sq_nonneg ( (1 - p) - (0.3 : ℝ) / 2 ), 
        sq_nonneg ( (1 - p) ), sq_nonneg ( (1 - p) - 0.3 ), 
        hp.1, hp.2]
    linarith