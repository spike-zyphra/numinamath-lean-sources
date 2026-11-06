import Mathlib

theorem algebra_278543 (n : ℕ) :
    ∑ i ∈ Finset.range n, (-1 : ℝ)^i * (i + 1)^2 =
    (-1 : ℝ)^(n - 1) * n * (n + 1) / 2 := by 
  cases n with
  | zero =>
    simp
  | succ n =>
    rw [Finset.sum_range_succ, algebra_278543 n]
    cases n with
    | zero =>
      norm_num
    | succ n =>
      simp [pow_two, pow_succ, mul_add, mul_comm] at *
      ring_nf
      <;> field_simp
      <;> ring