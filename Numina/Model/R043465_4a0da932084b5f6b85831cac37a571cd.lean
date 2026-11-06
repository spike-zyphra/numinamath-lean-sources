import Mathlib

open Real

lemma lemma_1 (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by
  have h1 : ∀ (i : ℕ), i ≥ 1 → 1 / (sqrt i + sqrt (i + 1)) = sqrt (i + 1) - sqrt i := by
    intro i hi
    have h2 : sqrt i ≥ 0 := Real.sqrt_nonneg (i : ℝ)
    have h3 : sqrt (i + 1) ≥ 0 := Real.sqrt_nonneg ((i + 1 : ℝ))
    have h4 : sqrt i + sqrt (i + 1) > 0 := by
      have h5 : sqrt (i + 1) > 0 := by
        apply Real.sqrt_pos.mpr
        have h6 : (i + 1 : ℝ) > 0 := by
          have : (i : ℝ) ≥ (1 : ℝ) := by exact_mod_cast (show i ≥ 1 by omega)
          nlinarith
        linarith
      linarith [show sqrt i ≥ 0 by apply Real.sqrt_nonneg]
    field_simp [(show sqrt i + sqrt (i + 1) ≠ 0 by linarith [h4])]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (i : ℝ) by positivity),
          Real.sq_sqrt (show (0 : ℝ) ≤ (i + 1 : ℝ) by positivity),
          Real.sqrt_nonneg (i : ℝ), Real.sqrt_nonneg ((i + 1 : ℝ)),
          sq_nonneg (sqrt (i + 1) - sqrt i)
          ]
  have h2 : ∀ (k : ℕ), ∑ i ∈ Finset.Icc 1 k, (1 / (sqrt i + sqrt (i + 1))) = sqrt (k + 1) - 1 := by
    intro k
    induction k with
    | zero =>
      norm_num
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      have h3 := h1 (k + 1) (by linarith)
      rw [h3]
      field_simp
      <;> ring_nf
  specialize h2 n
  simpa using h2


theorem algebra_195050 {n : ℕ} (hn : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = 2015 ↔ n = 4064255 := by
  constructor
  · -- Forward implication: if the sum equals 2015, then n = 4064255
    intro h_eq
    have h1 : ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1 : ℝ) - 1 := by
      apply lemma_1 n
      linarith
    rw [h1] at h_eq
    have h2 : sqrt (n + 1 : ℝ) = (2016 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (n + 1 : ℝ)]
    have h3 : (n + 1 : ℝ) = (2016 : ℝ) ^ 2 := by
      calc
        (n + 1 : ℝ) = (sqrt (n + 1 : ℝ)) ^ 2 := by
          rw [Real.sq_sqrt]
          positivity
        _ = (2016 : ℝ) ^ 2 := by 
          rw [h2]
    have h5 : (n + 1 : ℕ) = 2016 ^ 2 := by
      exact_mod_cast (show (n + 1 : ℝ) = (2016 : ℝ) ^ 2 by nlinarith)
    have h6 : n = 4064255 := by
      omega
    assumption
  · -- Backward implication: if n = 4064255, then the sum equals 2015
    intro h_eq
    rw [h_eq]
    have h1 : ∑ i ∈ Finset.Icc 1 (4064255 : ℕ), (1 / (sqrt i + sqrt (i + 1))) = sqrt (4064255 + 1 : ℝ) - 1 := by
      apply lemma_1 4064255
      all_goals
        norm_num
    rw [h1]
    have h2 : sqrt ((4064255 + 1 : ℝ)) = (2016 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
    rw [h2]
    all_goals
      norm_num