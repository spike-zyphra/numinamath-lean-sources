import Mathlib

/- Show that 91 is a pseudoprime to the base 3.-/
theorem number_theory_4818 {n a : ℕ} (hn : n = 91) (ha : a = 3) :
    a^(n-1) ≡ 1 [MOD n] := by
--    4. Now we combine the results using the Chinese Remainder Theorem:
-- - We have \( 3^{90} \equiv 1 \mod 7 \) and \( 3^{90} \equiv 1 \mod 13 \).
-- - Since both congruences are satisfied, we conclude that \( 3^{90} \equiv 1 \mod 91 \).
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  simp [hn]
  rw [show 91 = 7*13 by norm_num]
  rw [← Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)]
  constructor
--    - For \( 3^{90} \mod 7 \):
-- - First, we find the order of 3 modulo 7. The powers of 3 modulo 7 are:
-- - \( 3^1 \equiv 3 \)
-- - \( 3^2 \equiv 2 \)
-- - \( 3^3 \equiv 6 \)
-- - \( 3^4 \equiv 4 \)
-- - \( 3^5 \equiv 5 \)
-- - \( 3^6 \equiv 1 \)
-- - The order is 6, so \( 3^{90} \mod 7 \) can be simplified as follows:
-- - \( 90 \mod 6 = 0 \)
-- - Therefore, \( 3^{90} \equiv 1 \mod 7 \).
  . have : (a : ZMod 7) ≠ 0 := by
      rw [ha]
      exact Ne.symm (ne_of_beq_false rfl)
    have := ZMod.pow_card_sub_one_eq_one this
    simp at this
    rw [← ZMod.eq_iff_modEq_nat, show 90 = 6*15 by norm_num, pow_mul]
    push_cast
    rw [this, one_pow]
--    - For \( 3^{90} \mod 13 \):
-- - The powers of 3 modulo 13 are:
-- - \( 3^1 \equiv 3 \)
-- - \( 3^2 \equiv 9 \)
-- - \( 3^3 \equiv 1 \)
-- - The order is 3, so \( 3^{90} \mod 13 \) can be simplified as follows:
-- - \( 90 \mod 3 = 0 \)
-- - Therefore, \( 3^{90} \equiv 1 \mod 13 \).
  have : (a : ZMod 13) ^ 3 = 1 := by rw [ha]; rfl
  rw [← ZMod.eq_iff_modEq_nat, show 90 = 3 * 30 by norm_num, pow_mul]
  push_cast
  rw [this, one_pow]
