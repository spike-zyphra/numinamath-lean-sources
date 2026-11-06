import Mathlib

/- Show that if \( p \) and \( q \) are distinct primes, then \( p^{q-1} + q^{p-1} \equiv 1 \mod (pq) \).-/
theorem number_theory_4792 (p q : ℕ) (h₀ : p.Prime) (h₁ : q.Prime) (h₂ : p ≠ q) :
    (p^(q - 1) + q^(p - 1)) % (p * q) = 1:= by
  have hpge : 2 ≤ p := Nat.Prime.two_le h₀
  have hqge : 2 ≤ q := Nat.Prime.two_le h₁
  have hnge2 {n : ℕ} (hn : 2 ≤ n) : n-1=n-2+1 := by
    simp
    rw [Nat.sub_add_cancel hn]
  have hpcoq : p.Coprime q := by
    rw [Nat.coprime_primes]
    all_goals assumption
  have hpn : IsCoprime (q : ℤ) (p : ℤ) := by
    symm
    rw [Int.coprime_iff_nat_coprime]
    simp
    assumption
  have hqn : IsCoprime (p : ℤ) (q : ℤ) := by
    rw [Int.coprime_iff_nat_coprime]
    simp
    assumption
  have hp := Int.ModEq.pow_card_sub_one_eq_one h₀ hpn
  have hq := Int.ModEq.pow_card_sub_one_eq_one h₁ hqn
  --  4. **Combine results modulo \( p \)**: Therefore, we can combine the results:
  --  \[
  --  p^{q-1} + q^{p-1} \equiv 0 + 1 \equiv 1 \mod p.
  --  \]
  have h1 : p^(q-1)+q^(p-1) ≡ 1 [MOD p] := by
    nth_rw 3 [← zero_add 1]
    apply Nat.ModEq.add
    --        3. **Calculate \( q^{p-1} \mod p \)**: By Fermat's Little Theorem, since \( q \) is not divisible by \( p \):
-- \[
-- q^{p-1} \equiv 1 \mod p.
-- \]
    . rw [Nat.modEq_zero_iff_dvd]
      rw [hnge2 hqge, pow_succ]
      apply Nat.dvd_mul_left
--      2. **Calculate \( p^{q-1} \mod p \)**: Since \( p^{q-1} \) is clearly divisible by \( p \), we have:
-- \[
-- p^{q-1} \equiv 0 \mod p.
-- \]
    rw [Int.modEq_iff_dvd] at hp
    rw [Nat.modEq_iff_dvd]
    push_cast
    assumption
  --  7. **Combine results modulo \( q \)**: Thus, we have:
  --  \[
  --  p^{q-1} + q^{p-1} \equiv 0 + 1 \equiv 1 \mod q.
  --  \]
  have h2 : p^(q-1)+q^(p-1) ≡ 1 [MOD q] := by
    nth_rw 3 [← add_zero 1]
    apply Nat.ModEq.add
--      6. **Calculate \( q^{p-1} \mod q \)**: By Fermat's Little Theorem, since \( p \) is not divisible by \( q \):
-- \[
-- q^{p-1} \equiv 1 \mod q.
-- \]
    . rw [Int.modEq_iff_dvd] at hq
      rw [Nat.modEq_iff_dvd]
      push_cast
      assumption
--      5. **Calculate \( p^{q-1} \mod q \)**: Similarly, since \( p^{q-1} \) is divisible by \( q \):
-- \[
-- p^{q-1} \equiv 0 \mod q.
-- \]
    rw [Nat.modEq_zero_iff_dvd]
    rw [hnge2 hpge, pow_succ]
    apply Nat.dvd_mul_left
--    8. **Use the Chinese Remainder Theorem**: We have shown that:
-- \[
-- p^{q-1} + q^{p-1} \equiv 1 \mod p
-- \]
-- and
-- \[
-- p^{q-1} + q^{p-1} \equiv 1 \mod q.
-- \]
-- Since \( p \) and \( q \) are distinct primes, by the Chinese Remainder Theorem, this implies:
-- \[
-- p^{q-1} + q^{p-1} \equiv 1 \mod (pq).
-- \]
  conv_rhs => rw [show 1 = 1 % (p*q) by symm; apply Nat.mod_eq_of_lt; nlinarith]
  change _ ≡ _ [MOD _]
  rw [← Nat.modEq_and_modEq_iff_modEq_mul hpcoq]
  exact ⟨h1, h2⟩
