import Mathlib
/-- How many digits are in the base-ten representation of $8^5 \cdot 5^{10} \cdot 15^5$?
    (A) 14(B) 15(C) 16(D) 17(E) -/

theorem number_theory_94424 : (Nat.digits 10 (8^5 * 5^10 * 15^5)).length = 18 := by
  -- The number of digits are given by the logarithm to base 10.
  rw[Nat.digits_len _ _ (by norm_num) (by norm_num)]
  -- Prime factoring gives us $2^{15} \cdot 3^5 \cdot 5^{15}$ via
  -- decomposing 8,
  have : 8 ^ 5 = 2 ^ 15 := by
    have : 8 = 2^3 := by norm_num
    rw[this, ← pow_mul]
  rw[this]
  -- decomposing 15,
  have : 15 ^ 5 = 5 ^ 5 * 3 ^ 5 := by
    rw[← mul_pow]
    congr
  rw[this]
  change Nat.log 10 (2 ^ 15 * 5 ^ 10 * (5 ^ 5 * 3 ^ 5)) + 1 = 17 + 1
  congr
  -- recombining gives us $10^15 \cdot 243$,
  have : 2 ^ 15 * 5 ^ 10 * (5 ^ 5 * 3 ^ 5) = 2^15 * 5^15 * 243 := by
    rw[mul_assoc, mul_assoc, ← mul_assoc (5^10), ← pow_add]
    congr
  rw[this, ← mul_pow]
  -- hence the log is 17 due to this being between 10^18 and 10^19,
  -- and we can see the number has 18 digits.
  change Nat.log 10 (10^15 * 243) = 17
  rw[Nat.log_eq_iff (Or.inl (by norm_num))]
  constructor
  · norm_num
  · norm_num