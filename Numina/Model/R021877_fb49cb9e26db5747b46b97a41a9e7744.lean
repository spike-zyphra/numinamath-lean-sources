import Mathlib

theorem algebra_227592 (n : ℕ) (x : ℝ) :
    ∏ i ∈ Finset.range (n + 1), (1 + x ^ (2 ^ i)) = ∑ i ∈ Finset.range (2 ^ (n + 1)), x ^ i := by
  induction n with
  | zero =>
    simp [Finset.prod_range_succ, Finset.sum_range_succ]
    all_goals ring
  | succ n ih =>
    rw [Finset.prod_range_succ]
    rw [ih]
    have h1 : ∑ i ∈ Finset.range (2 ^ (n + 1 + 1)), x ^ i = 
      (∑ i ∈ Finset.range (2 ^ (n + 1)), x ^ i) + (∑ i ∈ Finset.range (2 ^ (n + 1)), x ^ (i + 2 ^ (n + 1)))
      := by
      rw [show 2 ^ (n + 1 + 1) = 2 ^ (n + 1) + 2 ^ (n + 1) by ring]
      rw [Finset.sum_range_add]
      <;> simp [Finset.sum_congr]
      <;> try ring_nf <;> simp [pow_add]
      <;> ring
    have h2 : (∑ i ∈ Finset.range (2 ^ (n + 1)), x ^ (i + 2 ^ (n + 1))) = (∑ i ∈ Finset.range (2 ^ (n + 1)), x ^ i) * x ^ (2 ^ (n + 1)) := by
      simp [Finset.sum_mul, pow_add]
      <;> ring_nf <;> simp [pow_add]
      <;> ring
    rw [h1, h2]
    all_goals ring