import Mathlib

open Real

lemma lemma_1 (n : ℕ) (hn : 0 < n) : ∑ i in Finset.Icc 1 n, (Real.sqrt (i + 1) - Real.sqrt i) = Real.sqrt (n + 1) - 1 := by
  have h1 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, (Real.sqrt (i + 1) - Real.sqrt i) = Real.sqrt (n + 1) - 1 := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp
      <;> ring
  specialize h1 n
  simpa using h1


theorem algebra_195372 {n : ℕ} (hn : n > 0) :
    ∑ i ∈ Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1)) : ℝ) = 2011 ↔ n = 4048143 := by
  constructor
  · -- Assume sum equals 2011, prove n = 4048143
    intro h_eq
    have h1 : ∀ (i : ℕ), (1 / (sqrt i + sqrt (i + 1)) : ℝ) = Real.sqrt (i + 1) - Real.sqrt i := by
      intro i
      have h2 : (sqrt i + sqrt (i + 1) : ℝ) ≠ 0 := by
        have h3 : Real.sqrt i ≥ 0 := Real.sqrt_nonneg (i : ℝ)
        have h4 : Real.sqrt (i + 1) > 0 := by
          have h5 : (i + 1 : ℝ) > 0 := by
            have : (i : ℝ) ≥ 0 := by exact_mod_cast show (0 : ℕ) ≤ i by omega
            nlinarith
          have h6 : Real.sqrt (i + 1) > 0 := by
            apply Real.sqrt_pos.mpr
            linarith
          linarith
        have h7 : (sqrt i + sqrt (i + 1) : ℝ) > 0 := by linarith [h3, h4]
        linarith
      field_simp [h2]
      have h8 : Real.sqrt (i + 1) ^ 2 = (i + 1 : ℝ) := Real.sq_sqrt (by linarith)
      have h9 : Real.sqrt i ^ 2 = (i : ℝ) := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg (i : ℝ), Real.sqrt_nonneg (i + 1 : ℝ)]
    have h2 : ∑ i in Finset.Icc 1 n, (1 / (sqrt i + sqrt (i + 1)) : ℝ) = ∑ i in Finset.Icc 1 n, (Real.sqrt (i + 1) - Real.sqrt i : ℝ) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        specialize h1 i
        simpa using h1
    rw [h2] at h_eq
    have h3 : ∑ i in Finset.Icc 1 n, (Real.sqrt (i + 1) - Real.sqrt i : ℝ) = Real.sqrt (n + 1 : ℝ) - 1 := by
      have h4 : 0 < (n : ℝ) := by exact_mod_cast show (0 : ℕ) < n by linarith
      have h5 : ∑ i in Finset.Icc 1 n, (Real.sqrt (i + 1) - Real.sqrt i : ℝ) = Real.sqrt (n + 1 : ℝ) - 1 := lemma_1 n (by linarith)
      simpa using h5
    rw [h3] at h_eq
    have h4 : Real.sqrt (n + 1 : ℝ) = (2012 : ℝ) := by linarith
    have h5 : (n + 1 : ℝ) = (2012 : ℝ) ^ 2 := by
      calc
        (n + 1 : ℝ) = (Real.sqrt (n + 1 : ℝ)) ^ 2 := by rw [Real.sq_sqrt]; positivity
        _ = (2012 : ℝ) ^ 2 := by rw [h4]
    have h8 : (n + 1 : ℕ) = 2012 ^ 2 := by
      have h9 : (n + 1 : ℝ) = (2012 ^ 2 : ℝ) := by
        linarith
      exact_mod_cast h9
    have h10 : n = 4048143 := by
      omega
    exact h10
  · -- Assume n = 4048143, prove sum = 2011
    intro h_eq
    rw [h_eq]
    have h1 : ∀ (i : ℕ), (1 / (sqrt i + sqrt (i + 1)) : ℝ) = Real.sqrt (i + 1) - Real.sqrt i := by
      intro i
      have h2 : (sqrt i + sqrt (i + 1) : ℝ) ≠ 0 := by
        have h3 : Real.sqrt i ≥ 0 := Real.sqrt_nonneg (i : ℝ)
        have h4 : Real.sqrt (i + 1) > 0 := by
          have h5 : (i + 1 : ℝ) > 0 := by
            have : (i : ℝ) ≥ 0 := by exact_mod_cast show (0 : ℕ) ≤ i by omega
            nlinarith
          have h6 : Real.sqrt (i + 1) > 0 := by
            apply Real.sqrt_pos.mpr
            linarith
          linarith
        have h7 : (sqrt i + sqrt (i + 1) : ℝ) > 0 := by linarith [h3, h4]
        linarith
      field_simp [h2]
      have h8 : Real.sqrt (i + 1) ^ 2 = (i + 1 : ℝ) := Real.sq_sqrt (by linarith)
      have h9 : Real.sqrt i ^ 2 = (i : ℝ) := Real.sq_sqrt (by linarith)
      nlinarith [Real.sqrt_nonneg (i : ℝ), Real.sqrt_nonneg (i + 1 : ℝ)]
    have h2 : ∑ i in Finset.Icc 1 (4048143 : ℕ), (1 / (sqrt i + sqrt (i + 1)) : ℝ) = ∑ i in Finset.Icc 1 (4048143 : ℕ), (Real.sqrt (i + 1) - Real.sqrt i : ℝ) := by
      apply Finset.sum_congr
      · rfl
      · intro i hi
        specialize h1 i
        simpa using h1
    rw [h2]
    have h3 : ∑ i in Finset.Icc 1 (4048143 : ℕ), (Real.sqrt (i + 1) - Real.sqrt i : ℝ) = Real.sqrt (4048143 + 1 : ℝ) - 1 := by
      have h4 : 0 < (4048143 : ℕ) := by norm_num
      have h5 : ∑ i in Finset.Icc 1 (4048143 : ℕ), (Real.sqrt (i + 1) - Real.sqrt i : ℝ) = Real.sqrt ((4048143 : ℕ) + 1 : ℝ) - 1 := lemma_1 4048143 (by norm_num)
      simpa using h5
    rw [h3]
    have h4 : Real.sqrt (4048143 + 1 : ℝ) = (2012 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h4]
    all_goals norm_num