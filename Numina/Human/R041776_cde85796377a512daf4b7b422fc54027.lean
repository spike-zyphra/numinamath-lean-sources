import Mathlib

/- $\underline{\text { Meizus S.I. }}$

The sum $3^{1974}+2^{1974}$ is divisible by 13. Prove this. -/
theorem number_theory_227331 : 13 ∣ 3^1974 + 2^1974 := by
  -- Halve the exponent
  rw [show 1974 = 2 * 987 by norm_num, pow_mul, pow_mul]
  rw [show 3 ^ 2 = 9 by norm_num, show 2 ^ 2 = 4 by norm_num]
  rw [show 13 = 9 + 4 by norm_num]
  -- Show that 987 is odd
  have odd_exp : Odd 987 := by use 493; norm_num
  -- Use the lemma x + y ∣ x ^ n + y ^ n when n is odd
  exact Odd.nat_add_dvd_pow_add_pow 9 4 odd_exp