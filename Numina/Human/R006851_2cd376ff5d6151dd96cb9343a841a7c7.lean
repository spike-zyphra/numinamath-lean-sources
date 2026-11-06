import Mathlib

-- we compute the first sum by induction
lemma lemma_1 (k: ℕ) (hk: 0 < k):
  ∑ i ∈ Finset.range k, 2 ^ (6 * i) = (64 ^ k - 1) / (63: ℚ) := by
  induction' k with k ih
  .
    simp at hk
  .
    by_cases l: k = 0
    .
      simp [l]
      field_simp
      ring
    .
      simp at l
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring_nf
      have f: 2 ^ (k * 6) = (64: ℚ) ^ k := by
        rw [show k * 6 = 6 * k by ring]
        rw [pow_mul]
        ring
      rw [f]
      clear f
      ring
      omega

-- we compute the second sum by induction
lemma lemma_2 (k: ℕ) (hk: 0 < k):
  ∑ i ∈ Finset.range k, 8 ^ (2 * i) = (64 ^ k - 1) / (63: ℚ) := by
  induction' k with k ih
  .
    simp at hk
  .
    by_cases l: k = 0
    .
      simp [l]
      field_simp
      ring
    .
      simp at l
      rw [Finset.sum_range_succ, ih]
      field_simp
      ring_nf
      have f: 8 ^ (k * 2) = (64: ℚ) ^ k := by
        rw [show k * 2 = 2 * k by ring]
        rw [pow_mul]
        ring
      rw [f]
      clear f
      ring
      omega


/-Let $k$ be a positive integer. Let $N_k$ be the binary number formed by $k$ repetitions of the binary block '100101'.
For example, if $k=2$, $N_2$ is $100101100101_2$. Determine the representation of $N_k$ in base eight.
Show the answer is the number whose base eight representation consists of $k$ repetitions of the block of digits '45'
(e.g., for $k=2$, this is $4545_8$).
-/
theorem number_theory_641727 (k N_k: ℕ) (hk: 0 < k) (hN: N_k = (1 + 2^2 + 2^5) * ∑ i ∈ Finset.range k, 2 ^ (6 * i)):
  N_k = (5 + 4 * 8) * ∑ i ∈ Finset.range k, 8 ^ (2 * i) := by

  rw [hN]
  clear hN
  qify
  rw [lemma_1 k hk]
  rw [lemma_2 k hk]
  ring
