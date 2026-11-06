import Mathlib

theorem number_theory_157898 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧
      ∃ a b c d e f : ℤ,
        n = a^2 + b^2 ∧
        n + 1 = c^2 + d^2 ∧
        n + 2 = e^2 + f^2 := by
  intro N
  use 4 * (N + 1)^4 + 4 * (N + 1)^2
  constructor
  · -- Show that n > N
    nlinarith [sq_nonneg (N : ℤ), sq_nonneg (N + 1 : ℤ), sq_nonneg (N - 1 : ℤ)]
  · -- Now we need to prove the existence of a,b,c,d,e,f integers such that the equations hold
    use 2 * (N + 1)^2, 2 * (N + 1)
    use 2 * (N + 1)^2 + 1, 0
    use 2 * (N + 1)^2 + 1, 1
    constructor
    · -- Show that n = a^2 + b^2
      ring_nf
      <;> norm_num
      <;> ring
    constructor
    · -- Show that n + 1 = c^2 + d^2
      ring_nf
      <;> norm_num
      <;> ring
    · -- Show that n + 2 = e^2 + f^2
      ring_nf
      <;> norm_num
      <;> ring