import Mathlib

/- Call a positive integer in base 10k-good if we can split it into two integers y and z ,
such that y is all digits on the left and z is all digits on the right, and such that
y=k⋅z. For example, 2010 is 2 -good because we can split it into 20 and 10 and
20=2⋅10.20010 is also 2 -good, because we can split it into 20 and 010 .
In addition, it is 20 -good, because we can split it into 200 and 10 . Show that there exists a 48 -good perfect square.-/
def is_square (n: ℕ): Prop := ∃ m: ℕ, (n = m ^ 2) ∧ (0 < m)

theorem number_theory_608704: ∃ a z: ℕ, (is_square (48 * z * 10 ^ a + z)) ∧ (z < 10 ^ a) := by
  use 42
  use (48 * 10 ^ 42 + 1) / 49
  constructor
  · -- Show that 48 * z * 10 ^ 42 + z is a perfect square
    unfold is_square
    use (48 * 10 ^ 42 + 1) / 7
    constructor
    · -- Show equality
      norm_num
      <;> ring_nf
      <;> omega
    · -- Show positivity
      norm_num
  · -- Show that z < 10 ^ 42
    norm_num