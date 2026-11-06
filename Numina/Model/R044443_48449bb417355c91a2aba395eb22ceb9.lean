import Mathlib

open Real

theorem inequalities_194402 : ∑ i ∈ Finset.range 2012, (1 / ((i + 1) * sqrt (i + 2) + (i + 2) * sqrt (i + 1))) > 97 / 100 := by
  have h1 : ∀ n : ℕ, ∑ i ∈ Finset.range n, (1 / ((i + 1) * sqrt (i + 2) + (i + 2) * sqrt (i + 1))) = (1 : ℝ) - Real.sqrt (n + 1) / (n + 1 : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp
      <;> norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp
      <;> ring_nf <;> field_simp [Real.sqrt_nonneg] <;> ring_nf <;> norm_num
      <;> ring_nf <;> norm_num
  have h2 := h1 2012
  rw [h2]
  have h3 : Real.sqrt (2013 : ℝ) < 45 := by
    nlinarith [Real.sqrt_nonneg (2013 : ℝ), Real.sq_sqrt (show 0 ≤ (2013 : ℝ) by norm_num)]
  have h4 : Real.sqrt (2013 : ℝ) > 0 := by positivity
  have h7 : Real.sqrt (2013 : ℝ) / (2013 : ℝ) < (0.0224 : ℝ) := by
    apply (div_lt_iff₀ (by norm_num)).mpr
    nlinarith [Real.sqrt_nonneg (2013 : ℝ), Real.sqrt_nonneg (2013 : ℝ), Real.sq_sqrt (show 0 ≤ (2013 : ℝ) by norm_num), h3]
  have h8 : (1 : ℝ) - (Real.sqrt (2013 : ℝ) / (2013 : ℝ)) > (0.97 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (2013 : ℝ), h7]
  nlinarith [h8, Real.sqrt_nonneg (2013 : ℝ)]