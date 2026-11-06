import Mathlib

theorem algebra_116005 (n : ℕ) :
    ∑ i in Finset.range n, (-1 : ℝ)^i * (i + 1)^2 =
    (-1 : ℝ)^(n - 1) * n * (n + 1) / 2 := by
  cases n with
  | zero =>
    simp
  | succ n =>
    rw [Finset.sum_range_succ, algebra_116005 n]
    cases n with
    | zero =>
      norm_num
    | succ n =>
      simp [pow_succ, mul_add, add_mul]
      ring_nf
      <;> field_simp
      <;> ring_nf <;> field_simp
      <;> linarith