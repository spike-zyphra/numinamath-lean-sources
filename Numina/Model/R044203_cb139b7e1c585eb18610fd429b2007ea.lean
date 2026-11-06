import Mathlib

theorem algebra_321812 (x : ℝ) (h : Real.sin x ^ 4 / 3 + Real.cos x ^ 4 / 7 = 1 / 10)
    (n : ℕ) (hn : n > 0) :
    Real.sin x ^ (2 * n) / 3 ^ (n - 1) + Real.cos x ^ (2 * n) / 7 ^ (n - 1) = 1 / 10 ^ (n - 1) := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x ^ 2 = 3 / 10 := by
    have h_eq : Real.sin x ^ 4 / 3 + Real.cos x ^ 4 / 7 = 1 / 10 := h
    have h3 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      have : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := h1
      linarith
    have h4 : Real.cos x ^ 4 = (1 - Real.sin x ^ 2) ^ 2 := by
      calc
        Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 := by ring
        _ = (1 - Real.sin x ^ 2) ^ 2 := by rw [h3]
    rw [h4] at h_eq
    nlinarith [sq_nonneg (Real.sin x ^ 2 - 3 / 10)]
  have h3 : Real.cos x ^ 2 = 7 / 10 := by
    have h4 : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
      have : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := h1
      linarith
    rw [h4, h2]
    all_goals norm_num
  have h4 : Real.sin x ^ (2 * n) = (Real.sin x ^ 2) ^ n := by
    ring_nf
  have h5 : Real.cos x ^ (2 * n) = (Real.cos x ^ 2) ^ n := by
    ring_nf
  rw [h4, h5, h2, h3]
  cases n with
  | zero => 
    exfalso 
    linarith
  | succ n => 
    cases n with
    | zero => 
      norm_num
    | succ n => 
      norm_num [pow_succ, pow_mul] at *
      <;> field_simp at *
      <;> ring_nf
      <;> norm_num
      all_goals norm_num