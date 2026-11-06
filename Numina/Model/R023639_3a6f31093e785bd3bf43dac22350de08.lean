import Mathlib

open Real

theorem inequalities_193252 (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, (1 / sqrt i) ≥ sqrt n := by
  have h1 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, (1 / sqrt i) ≥ sqrt n := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      have h4 : ∑ i in Finset.Icc 1 n, (1 / sqrt i) ≥ sqrt (↑n : ℝ) := ih
      have h10 : (1 / sqrt ((↑n + 1 : ℝ)) ) ≥ sqrt ((↑n + 1 : ℝ)) - sqrt (↑n : ℝ) := by
        have h100 : sqrt ((↑n + 1 : ℝ)) > 0 := by
          apply Real.sqrt_pos.mpr
          linarith
        have h102 : (1 / sqrt ((↑n + 1 : ℝ)) ) ≥ sqrt ((↑n + 1 : ℝ)) - sqrt (↑n : ℝ) := by
          have h103 : sqrt ((↑n + 1 : ℝ)) - sqrt (↑n : ℝ) = 1 / (sqrt ((↑n + 1 : ℝ)) + sqrt (↑n : ℝ)) := by
            have h104 : sqrt ((↑n + 1 : ℝ)) + sqrt (↑n : ℝ) > 0 := by
              positivity
            field_simp
            nlinarith [Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg (↑n + 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 : ℝ) by linarith)]
          rw [h103]
          have h105 : sqrt ((↑n + 1 : ℝ)) + sqrt (↑n : ℝ) ≥ sqrt ((↑n + 1 : ℝ)) := by
            linarith [Real.sqrt_nonneg (↑n + 1 : ℝ), Real.sqrt_nonneg (↑n : ℝ)]
          have h106 : sqrt ((↑n + 1 : ℝ)) > 0 := by
            apply Real.sqrt_pos.mpr
            linarith
          have h107 : sqrt ((↑n + 1 : ℝ)) + sqrt (↑n : ℝ) > 0 := by
            positivity
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith [Real.sqrt_nonneg (↑n + 1 : ℝ), Real.sqrt_nonneg (↑n : ℝ)]
        linarith
      have h12 : ∑ i in Finset.Icc 1 n, (1 / sqrt i) + (1 / sqrt ((↑n + 1 : ℝ)) ) ≥ sqrt ((↑n + 1 : ℝ)) := by
        nlinarith [h4, h10, Real.sqrt_nonneg (↑n : ℝ), Real.sqrt_nonneg (↑n + 1 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (↑n + 1 : ℝ) by linarith)]
      simpa using h12
  specialize h1 n
  simpa using h1