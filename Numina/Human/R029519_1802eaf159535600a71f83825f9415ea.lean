import Mathlib

/- Let \( p \) be a prime number and let \( a \) be a positive integer that is not divisible by \( p \). We define the Fermat quotient \( q_{p}(a) \) as \( q_{p}(a) = \frac{a^{p-1} - 1}{p} \). Show that if \( a \) and \( b \) are positive integers not divisible by the prime \( p \), then \( q_{p}(ab) \equiv q_{p}(a) + q_{p}(b) \mod p \).-/
theorem number_theory_4808 {p a b : ℕ} (hp : p.Prime) (_ : 0 < a) (_ : 0 < b)
    (hpa : ¬p ∣ a) (hpb : ¬p ∣ b) :
    ((a*b)^(p-1)-1)/p ≡ (a^(p-1)-1)/p + (b^(p-1)-1)/p [ZMOD p] := by
  have hacop : IsCoprime (a : ℤ) (p : ℤ) := by
    symm
    rw [Int.coprime_iff_nat_coprime]
    simp
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    assumption
  have hbcop : IsCoprime (b : ℤ) (p : ℤ) := by
    symm
    rw [Int.coprime_iff_nat_coprime]
    simp
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    assumption
  have habcop : IsCoprime (a*b : ℤ) (p : ℤ) := by
    symm
    rw [Int.coprime_iff_nat_coprime, Int.natAbs_mul]
    simp
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    exact Nat.Prime.not_dvd_mul hp hpa hpb
--    4. **Use the fact that \( a^{p-1} \equiv 1 \mod p \) and \( b^{p-1} \equiv 1 \mod p \)** (by Fermat's Little Theorem, since \( a \) and \( b \) are not divisible by \( p \)):
-- \[
-- a^{p-1} - 1 \equiv 0 \mod p \quad \text{and} \quad b^{p-1} - 1 \equiv 0 \mod p
-- \]
  have hapow := Int.ModEq.pow_card_sub_one_eq_one hp hacop
  have hbpow := Int.ModEq.pow_card_sub_one_eq_one hp hbcop
  have habpow := Int.ModEq.pow_card_sub_one_eq_one hp habcop
  rw [Int.modEq_iff_dvd, dvd_sub_comm] at hapow hbpow habpow
--    5. **Now, express \( a^{p-1} b^{p-1} - 1 \)**:
-- \[
-- a^{p-1} b^{p-1} - 1 = (a^{p-1} - 1) + (b^{p-1} - 1) + (a^{p-1} - 1)(b^{p-1} - 1)
-- \]
  have H : (a*b)^(p-1)-(1 : ℤ) = (a^(p-1)-1)*(b^(p-1)-1) +
    (a^(p-1)-1) + (b^(p-1)-1) := by ring
  rw [H, Int.add_ediv_of_dvd_right hbpow, Int.add_ediv_of_dvd_right hapow, Int.modEq_iff_dvd]
  simp
  apply Int.dvd_div_of_mul_dvd
--    8. **Now, consider the term \( \frac{(a^{p-1} - 1)(b^{p-1} - 1)}{p} \)**. Since both \( a^{p-1} - 1 \) and \( b^{p-1} - 1 \) are divisible by \( p \), their product is divisible by \( p^2 \). Thus, this term is congruent to \( 0 \mod p \):
-- \[
-- \frac{(a^{p-1} - 1)(b^{p-1} - 1)}{p} \equiv 0 \mod p
-- \]
  apply Int.mul_dvd_mul
  all_goals assumption
