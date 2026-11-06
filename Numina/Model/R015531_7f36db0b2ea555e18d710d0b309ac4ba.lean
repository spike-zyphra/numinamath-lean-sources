import Mathlib

open Real

theorem algebra_297927 : ∑ i ∈ Finset.range 2005, (1 / (sqrt (i + 1) + sqrt (i + 2))) = sqrt 2006 - 1 := by
  have h1 : ∀ (i : ℕ), 1 / (sqrt (i + 1) + sqrt (i + 2)) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) ≥ 0 := Real.sqrt_nonneg (i + 1)
    have h3 : sqrt (i + 2) ≥ 0 := Real.sqrt_nonneg (i + 2)
    have h4 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by
      by_contra h
      have h5 : sqrt (i + 1) ≥ 0 := Real.sqrt_nonneg (i + 1)
      have h6 : sqrt (i + 2) ≥ 0 := Real.sqrt_nonneg (i + 2)
      have h7 : sqrt (i + 1) = 0 := by linarith [h5, h6, h]
      have h8 : sqrt (i + 2) = 0 := by linarith [h5, h6, h, h7]
      have h9 : (i + 1 : ℝ) = 0 := by
        calc
          (i + 1 : ℝ) = (sqrt (i + 1)) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = (0) ^ 2 := by rw [h7]
          _ = (0 : ℝ) := by norm_num
      have h10 : (i : ℝ) = (-1 : ℝ) := by
        nlinarith
      have h11 : (i : ℝ) ≥ (0 : ℝ) := by
        exact_mod_cast (show (i : ℕ) ≥ 0 by omega)
      linarith [h10, h11]
    field_simp [h4]
    have h6 : sqrt (i + 1) ^ 2 = (i + 1 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    have h7 : sqrt (i + 2) ^ 2 = (i + 2 : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [Real.sqrt_nonneg (i + 1), Real.sqrt_nonneg (i + 2)]
  have h2 : ∀ (k : ℕ), ∑ i in Finset.range k, (1 / (sqrt (i + 1) + sqrt (i + 2))) = sqrt (k + 1) - 1 := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp [h1]
      <;> ring_nf <;> norm_num
  specialize h2 2005
  norm_num at h2 ⊢
  linarith