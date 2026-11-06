import Mathlib

open Real

theorem algebra_212429 (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = 100 ↔ n = 10200 := by
  constructor
  · -- Assume the sum equals 100, prove n = 10200
    intro h_eq
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (n + 1) - 1 := by 
      intro n 
      have h2 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (n + 1) - 1 := by 
        intro n 
        induction n with 
        | zero =>
          norm_num 
          <;> ring_nf 
          <;> norm_num 
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih]
          field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr (show (0 : ℝ) < (n + 1) by positivity), Real.sqrt_pos.mpr (show (0 : ℝ) < ((n + 1 : ℝ) + 1) by positivity)]
          <;> ring_nf 
          <;> rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
          <;> ring 
      exact h2 n 
    have eq1 : ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (n + 1) - 1 := h1 n 
    rw [eq1] at h_eq 
    have h2 : Real.sqrt (n + 1) = 101 := by linarith 
    have h3 : (n + 1 : ℝ) = (101 : ℝ) ^ 2 := by 
      calc 
        (n + 1 : ℝ) = (Real.sqrt (n + 1)) ^ 2 := by 
          rw [Real.sq_sqrt]
          linarith 
        _ = (101 : ℝ) ^ 2 := by 
          rw [h2]
    have h4 : (n + 1 : ℝ) = (10201 : ℝ) := by 
      norm_num at h3 ⊢ 
      linarith 
    have h5 : (n : ℝ) = (10200 : ℝ) := by 
      linarith 
    have h6 : n = 10200 := by 
      exact_mod_cast h5 
    exact h6 
  · -- Assume n = 10200, prove the sum equals 100 
    intro h_eq 
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (n + 1) - 1 := by 
      intro n 
      have h2 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (n + 1) - 1 := by 
        intro n 
        induction n with 
        | zero =>
          norm_num 
        | succ n ih =>
          rw [Finset.sum_Icc_succ_top (by linarith)]
          rw [ih]
          field_simp [add_mul, mul_add, pow_two, Real.sqrt_pos.mpr (show (0 : ℝ) < (n + 1) by positivity), Real.sqrt_pos.mpr (show (0 : ℝ) < ((n + 1 : ℝ) + 1) by positivity)]
          <;> ring_nf 
          <;> rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
          <;> ring 
      exact h2 n 
    have eq1 : ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = Real.sqrt (n + 1) - 1 := h1 n 
    rw [eq1] 
    have h5 : Real.sqrt ((n : ℝ) + 1) = (101 : ℝ) := by 
      rw [show (n : ℝ) = (10200 : ℝ) by exact_mod_cast h_eq]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
    nlinarith [h5]