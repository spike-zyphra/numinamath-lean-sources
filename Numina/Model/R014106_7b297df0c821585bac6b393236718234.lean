import Mathlib

open Real

theorem algebra_313171 {M N : ℝ}
    (hM : M = ∑ i ∈ Finset.range 1993, (1 / (sqrt (i + 1) + sqrt (i + 2))))
    (hN : N = ∑ i ∈ Finset.range 1994, (-1 : ℝ) ^ i * (i + 1)) :
    N / (M + 1) ^ 2 = -1 / 2 := by

  have h1 : M = Real.sqrt 1994 - 1 := by
    rw [hM]
    have h2 : ∀ n, ∑ i ∈ Finset.range n, (1 / (sqrt (i + 1) + sqrt (i + 2))) = sqrt (n + 1) - 1 := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [add_comm (sqrt ((n : ℝ) + 1)) (sqrt ((n : ℝ) + 2)), Real.sqrt_nonneg ((n : ℝ) + 1), Real.sqrt_nonneg ((n : ℝ) + 2), mul_nonneg (Real.sqrt_nonneg ((n : ℝ) + 1)) (Real.sqrt_nonneg ((n : ℝ) + 2))]
        <;> ring_nf <;> rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
        all_goals nlinarith [Real.sqrt_nonneg ((n : ℝ) + 1), Real.sqrt_nonneg ((n : ℝ) + 2)]
    specialize h2 1993
    norm_num at h2 ⊢
    linarith

  have h3 : N = -997 := by
    rw [hN]
    norm_num [Finset.sum_range_succ]

  rw [h1] at *
  rw [h3]

  have h4 : (Real.sqrt 1994 : ℝ) ^ 2 = (1994 : ℝ) := by
    rw [Real.sq_sqrt]
    all_goals
      norm_num

  field_simp [h4]
  all_goals
    nlinarith