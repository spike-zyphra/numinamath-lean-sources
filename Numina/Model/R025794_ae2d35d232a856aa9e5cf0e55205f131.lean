import Mathlib

theorem algebra_154865 {n : ℕ} (hn : 0 < n) (S1 S3 V2 V4 : ℤ)
    (hS1 : ∑ i in Finset.Icc 1 (2 * n), i = S1)
    (hS3 : ∑ i in Finset.Icc 1 (2 * n), i ^ 3 = S3)
    (hV2 : ∑ i in Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * i ^ 2 = V2)
    (hV4 : ∑ i in Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * i ^ 4 = V4) :
    V4 + 2 * V2 = S1 + 2 * S3 := by
  rw [show V4 = ∑ i in Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * i ^ 4 by rw [hV4]]
  rw [show V2 = ∑ i in Finset.Icc 1 (2 * n), (-1 : ℤ) ^ i * i ^ 2 by rw [hV2]]
  rw [show S1 = ∑ i in Finset.Icc 1 (2 * n), i by rw [hS1]]
  rw [show S3 = ∑ i in Finset.Icc 1 (2 * n), i ^ 3 by rw [hS3]]

  have h2 : ∀ k : ℕ, 0 < k → 
    (∑ i in Finset.Icc 1 (2 * k), (-1 : ℤ) ^ i * i ^ 4) + 2 * (∑ i in Finset.Icc 1 (2 * k), (-1 : ℤ) ^ i * i ^ 2) = 
    (∑ i in Finset.Icc 1 (2 * k), i) + 2 * (∑ i in Finset.Icc 1 (2 * k), i ^ 3) := by 
    intro k hk
    induction k with 
    | zero => 
      exfalso
      linarith
    | succ k ih =>
      cases k with
      | zero => 
        norm_num [Finset.sum_Icc_succ_top, pow_two, pow_succ, pow_zero]
        <;> ring_nf
        <;> norm_num
      | succ k => 
        have eq1 : ∑ i in Finset.Icc 1 (2 * (k + 1 + 1)), (-1 : ℤ) ^ i * i ^ 4 + 2 * ∑ i in Finset.Icc 1 (2 * (k + 1 + 1)), (-1 : ℤ) ^ i * i ^ 2 = 
          ∑ i in Finset.Icc 1 (2 * (k + 1 + 1)), i + 2 * ∑ i in Finset.Icc 1 (2 * (k + 1 + 1)), i ^ 3 := by
          have h2 := ih (show 0 < k + 1 by omega)
          have h3 := h2
          rw [show 2 * (k + 1 + 1) = 2 * (k + 1) + 1 + 1 by omega]
          -- Apply summation splitting
          simp [Finset.sum_Icc_succ_top, pow_two, pow_succ] at h3 ⊢
          ring_nf at h3 ⊢
          <;> norm_num [mul_add, pow_two, pow_succ] at h3 ⊢
          <;> try { 
            nlinarith [sq_nonneg (k + 1 : ℤ), sq_nonneg ((k + 1 : ℤ) + 1)]
          }
          <;> try { 
            ring_nf at h3 ⊢
            nlinarith [sq_nonneg (k + 1 : ℤ), sq_nonneg ((k + 1 : ℤ) + 1)]
          }
          <;> try { 
            linarith [sq_nonneg (k + 1 : ℤ), sq_nonneg ((k + 1 : ℤ) + 1)]
          }
          all_goals try { try { linarith } }
          <;> try { norm_num }
        exact eq1
  specialize h2 n hn
  linarith