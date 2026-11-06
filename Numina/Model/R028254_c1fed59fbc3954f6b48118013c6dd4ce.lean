import Mathlib

open Real

theorem inequalities_47829 : IsLeast {p | ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, sqrt (i ^ 2 + 1) ≤ (1 / 2) * n * (n + p)} (2 * √2 - 1) := by
  constructor
  · -- Show $2 \sqrt{2} - 1$ is in the set.
    intro n
    have h1 : ∀ n : ℕ, ∑ i ∈ Finset.Icc 1 n, sqrt (i ^ 2 + 1) ≤ (1 / 2) * n * (n + (2 * √2 - 1)) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        simp [ih] at *
        have h2 : sqrt ((n + 1 : ℝ) ^ 2 + 1) ≤ (n + Real.sqrt 2) := by
          have h3 : (n + 1 : ℝ) ^ 2 + 1 ≤ (n + Real.sqrt 2) ^ 2 := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num)]
          have h4 : sqrt ((n + 1 : ℝ) ^ 2 + 1) ≤ sqrt ((n + Real.sqrt 2) ^ 2) := by
            apply Real.sqrt_le_sqrt
            linarith
          have h5 : sqrt ((n + Real.sqrt 2) ^ 2) = (n + Real.sqrt 2) := by
            rw [Real.sqrt_sq (show 0 ≤ n + Real.sqrt 2 by positivity)]
          linarith [h4, h5, Real.sqrt_nonneg ((n + 1 : ℝ) ^ 2 + 1)]
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg ((n + 1 : ℝ) ^ 2 + 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (sqrt ((n + 1 : ℝ) ^ 2 + 1) - (n + Real.sqrt 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    specialize h1 n
    simpa using h1
  · -- Show $2 \sqrt{2} - 1$ is the smallest.
    intro p hp
    have h1 := hp 1
    norm_num [Finset.sum_Icc_succ_top] at h1
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]