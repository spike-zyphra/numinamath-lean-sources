import Mathlib

theorem algebra_318852 (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1)^3 = n^2 * (2 * n^2 - 1) := by
  cases n with
  | zero =>
    simp
  | succ n =>
    rw [Finset.sum_range_succ, algebra_318852 n]
    cases n with
    | zero =>
      simp [pow_succ, Nat.mul_add]
      <;> ring_nf <;> omega
    | succ n =>
      simp [pow_succ, Nat.mul_add]
      <;> ring_nf <;> omega