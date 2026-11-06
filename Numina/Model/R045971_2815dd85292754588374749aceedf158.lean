import Mathlib

open Real

theorem algebra_327610 : ∑ i ∈ Finset.range 2003, (1 / (sqrt (i + 1) + sqrt (i + 2))) = 2 * sqrt 501 - 1 := by
  have h1 : ∀ (i : ℕ), 1 / (sqrt (i + 1) + sqrt (i + 2)) = sqrt (i + 2) - sqrt (i + 1) := by
    intro i
    have h2 : sqrt (i + 1) + sqrt (i + 2) ≠ 0 := by
      have h3 : sqrt (i + 1) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      have h4 : sqrt (i + 2) > 0 := by
        apply Real.sqrt_pos.mpr
        linarith
      linarith
    field_simp [h2]
    have h3 : sqrt (i + 2) ^ 2 = i + 2 := Real.sq_sqrt (by linarith)
    have h4 : sqrt (i + 1) ^ 2 = i + 1 := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg (i + 1), Real.sqrt_nonneg (i + 2),
                sq_nonneg (sqrt (i + 2) - sqrt (i + 1)), sq_nonneg (sqrt (i + 2) + sqrt (i + 1))]
  rw [Finset.sum_congr rfl (fun i hi => h1 i)]
  have h3 : ∑ i in Finset.range 2003, (sqrt (i + 2) - sqrt (i + 1)) = sqrt 2004 - 1 := by
    have h7 : ∀ (n : ℕ), ∑ i in Finset.range n, (sqrt (i + 2) - sqrt (i + 1)) = sqrt (↑n + 1) - 1 := by
        intro n
        induction n with
        | zero =>
          simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          field_simp [Real.sqrt_nonneg (↑n + 1), Real.sqrt_nonneg (↑n + 2), Real.sqrt_nonneg (↑n + 3)]
          <;> nlinarith [Real.sqrt_nonneg (↑n + 1), Real.sqrt_nonneg (↑n + 2), Real.sqrt_nonneg (↑n + 3),
            Real.sq_sqrt (show (↑n + 1 : ℝ) ≥ 0 by linarith),
            Real.sq_sqrt (show (↑n + 2 : ℝ) ≥ 0 by linarith),
            Real.sq_sqrt (show (↑n + 3 : ℝ) ≥ 0 by linarith),
            mul_nonneg (Real.sqrt_nonneg (↑n + 1)) (Real.sqrt_nonneg (↑n + 2)) ]
    specialize h7 2003
    norm_num at h7 ⊢
    all_goals linarith
  rw [h3]
  have h5 : sqrt (2004 : ℝ) = 2 * sqrt 501 := by
    rw [show (2004 : ℝ) = (2 ^ 2 * 501 : ℝ) by norm_num]
    have h5 : sqrt (2 ^ 2 * 501 : ℝ) = (2 : ℝ) * sqrt 501 := by
      calc
        sqrt (2^2 * 501 : ℝ) = sqrt (2^2) * sqrt (501 : ℝ) := by
          rw [Real.sqrt_mul (by norm_num)]
        _ = (2 : ℝ) * sqrt (501 : ℝ) := by
          rw [show sqrt (2^2 : ℝ) = (2 : ℝ) by
            apply Real.sqrt_sq
            all_goals norm_num
          ]
        _ = (2 : ℝ) * sqrt 501 := by ring
    linarith [h5]
  rw [h5]
  all_goals ring_nf <;> norm_num
  <;> ring_nf <;> norm_num