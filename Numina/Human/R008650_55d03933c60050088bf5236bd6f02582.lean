import Mathlib

/- Using Fermat's little theorem, find the least positive residue of \(2^{1000000}\) modulo 17.-/
theorem number_theory_4782 : 2^1000000 = (1 : ZMod 17) := by
  -- To solve the problem, we will apply Fermat's little theorem, which states that if \(p\) is a prime number and \(a\) is an integer not divisible by \(p\), then \(a^{p-1} \equiv 1 \mod p\).
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  have : (2 : ZMod 17) ≠ 0 := Ne.symm (ne_of_beq_false rfl)
  have := ZMod.pow_card_sub_one_eq_one this
--   Now, we can rewrite \(2^{1000000}\) using the result from Fermat's theorem:
-- \[
-- 2^{1000000} = 2^{16 \cdot 62500} = (2^{16})^{62500}
-- \]
  rw [show 1000000 = 16 * 62500 by norm_num]
--   Using Fermat's theorem, we know that \(2^{16} \equiv 1 \mod 17\), so:
-- \[
-- (2^{16})^{62500} \equiv 1^{62500} \equiv 1 \mod 17
-- \]
  rw [pow_mul, this, one_pow]
