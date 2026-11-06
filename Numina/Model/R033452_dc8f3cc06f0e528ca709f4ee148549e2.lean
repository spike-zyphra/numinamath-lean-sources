import Mathlib

theorem algebra_250615 (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℤ)^i * (i + 1)^2 =
    (-1 : ℤ)^(n - 1) * (n * (n + 1)) / 2 := by
  cases n with
  | zero =>
    simp
  | succ n =>
    cases n with
    | zero =>
      norm_num
    | succ n =>
      rw [Finset.sum_range_succ, algebra_250615]
      cases n with
      | zero =>
        norm_num
        <;> ring_nf <;> omega
      | succ n =>
        simp [pow_two, mul_add, mul_comm]
        <;> ring_nf <;> omega