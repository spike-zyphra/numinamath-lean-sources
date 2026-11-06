import Mathlib

open Real

lemma lemma_1 (n : ℕ) (hn : 0 < n) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by

  have h1 : ∀ (i : ℕ), 1 / (sqrt i + sqrt (i + 1)) = sqrt (i + 1) - sqrt i := by
    intro i
    have h2 : sqrt (i : ℝ) ≥ 0 := Real.sqrt_nonneg (i : ℝ)
    have h3 : sqrt ((i + 1 : ℝ)) ≥ 0 := Real.sqrt_nonneg ((i + 1 : ℝ))
    have h4 : sqrt (i : ℝ) + sqrt ((i + 1 : ℝ)) > 0 := by
      have h5 : sqrt ((i + 1 : ℝ)) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith [show sqrt (i : ℝ) ≥ 0 by positivity, h5]
    field_simp [h2, h3]
    have h5 : sqrt ((i + 1 : ℝ)) ^ 2 = (i + 1 : ℝ) := Real.sq_sqrt (by linarith)
    have h6 : sqrt ((i : ℝ)) ^ 2 = (i : ℝ) := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (i : ℝ), Real.sqrt_nonneg ((i + 1 : ℝ)), sq_nonneg (sqrt ((i + 1 : ℝ)) - sqrt ((i : ℝ)))]
  have h2 : ∀ (n : ℕ), ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      rw [h1 (n + 1)]
      field_simp [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg ((n + 1 + 1 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 : ℝ) by positivity)]
      <;> nlinarith [Real.sqrt_nonneg (n + 1 : ℝ), Real.sqrt_nonneg ((n + 1 + 1 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 : ℝ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (n + 1 + 1 : ℝ) by positivity), sq_nonneg (sqrt ((n + 1 + 1 : ℝ)) - sqrt ((n + 1 : ℝ)))]
  specialize h2 n
  simpa using h2


theorem algebra_195450 {n : ℕ} (hn : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = 2010 ↔ n = 4044120 := by
  constructor
  · -- Assume the sum equals 2010, prove n = 4044120
    intro h_eq
    have h1 : ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by
      apply lemma_1 n
      all_goals omega
    rw [h1] at h_eq
    have h2 : sqrt ((n + 1 : ℝ)) = (2011 : ℝ) := by
      nlinarith [h_eq, Real.sqrt_nonneg (n + 1 : ℝ)]
    have h3 : (n + 1 : ℝ) = (2011 : ℝ) ^ 2 := by
      calc
        (n + 1 : ℝ) = (sqrt ((n + 1 : ℝ)) ) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (2011 : ℝ) ^ 2 := by rw [h2]
    have h4 : (n + 1 : ℕ) = 2011 ^ 2 := by
      have h5 : (n + 1 : ℝ) = (2011 : ℝ) ^ 2 := h3
      exact_mod_cast h5
    have h5 : n = 4044120 := by
      omega
    assumption
  · -- Assume n = 4044120, prove the sum equals 2010
    intro h_eq
    have h1 : ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1))) = sqrt (n + 1) - 1 := by
      apply lemma_1 n
      all_goals omega
    rw [h1]
    have h2 : n = 4044120 := by
      omega
    have h3 : (n + 1 : ℝ) = (2011 : ℝ) ^ 2 := by
      have h4 : (n : ℝ) = (4044120 : ℝ) := by
        exact_mod_cast h2
      nlinarith
    have h4 : sqrt ((n + 1 : ℝ)) = (2011 : ℝ) := by
      rw [show (n + 1 : ℝ) = (2011 : ℝ) ^ 2 by linarith [h3]]
      rw [Real.sqrt_sq]
      all_goals linarith
    nlinarith [h4, Real.sqrt_nonneg (n + 1 : ℝ)]