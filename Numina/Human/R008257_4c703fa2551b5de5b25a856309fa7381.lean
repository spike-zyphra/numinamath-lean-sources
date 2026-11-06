import Mathlib

/- Determine the last two digits of the number

$$
2^{5}+2^{5^{2}}+2^{5^{3}}+\cdots+2^{5^{1991}}
$$

written in decimal notation. -/
theorem number_theory_607933 : (∑ i ∈ Finset.range 1991, (2^(5^(i + 1)) : ℕ)) % 100 = 12 := by

  -- we first show that all numbers 2 ^ 5 ^ k modulo 100 equals 32 by induction
  have lem (k : ℕ) : 2 ^ (5 ^ (k + 1)) % 100 = 32 := by
    induction k
    case zero => norm_num
    case succ k ih =>
      rw [pow_add, pow_mul, Nat.pow_mod, ih, show 5 ^ 1 = 5 by norm_num]

  -- we need to prove a general theorem with k in place of 1991 in order to avoid 'deep kernel recursion'
  have gen_thm (k : ℕ) : (∑ i ∈ Finset.range k, (2^(5^(i + 1)) : ℕ)) % 100 = (32 * k) % 100 := by 
    rw [Finset.sum_nat_mod] -- move the mod operation inside the summation
    -- each summand is equal to 32 as shown by lem
    have : ∑ i ∈ Finset.range k, 2 ^ 5 ^ (i + 1) % 100 = ∑ i ∈ Finset.range k, 32 := by
      congr 
      ext i 
      rw [lem i]
    -- so the summation equals 32 * k
    rw [this, Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, mul_comm]

  -- finally we apply the general theorem to 1991 to prove the major goal.
  have spe_thm := gen_thm 1991
  rw [spe_thm]
