import Mathlib

/- Show that \(42\) divides \(n^{7} - n\) for all positive integers \(n\).-/
theorem number_theory_4789 (n : ℤ) (h₀ : n > 0) : 42 ∣ n^7 - n := by
  rw [Int.dvd_iff_emod_eq_zero]
  change _ ≡ 0 [ZMOD _]
--    1. **Divisibility by \(2\)**:
-- - If \(n\) is even, then \(n\) is divisible by \(2\).
-- - If \(n\) is odd, then both \(n^{3} - 1\) and \(n^{3} + 1\) are even (since the difference between them is \(2\)). Therefore, at least one of them is divisible by \(2\).
  have h1 : n^7-n ≡ 0 [ZMOD 2] := by
    rw [Int.modEq_zero_iff_dvd, ← even_iff_two_dvd]
    rw [show n^7-n=n*(n+1)*(n^2-n+1)*(n^3-1) by ring]
    apply Even.mul_right
    apply Even.mul_right
    exact Int.even_mul_succ_self _
--    2. **Divisibility by \(3\)**:
-- - We can check the values of \(n\) modulo \(3\):
-- - If \(n \equiv 0 \mod 3\), then \(n\) is divisible by \(3\).
-- - If \(n \equiv 1 \mod 3\), then \(n^{3} - 1 \equiv 0 \mod 3\).
-- - If \(n \equiv 2 \mod 3\), then \(n^{3} + 1 \equiv 0 \mod 3\).
-- - In all cases, \(n(n^{3} - 1)(n^{3} + 1)\) is divisible by \(3\).
  have h2 : n^7-n ≡ 0 [ZMOD 3] := by
    have : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
    have : n % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    interval_cases h : n % 3
    . rw [← sub_zero 0]
      apply Int.ModEq.sub ?_ (by exact h)
      rw [← zero_pow <| show 7 ≠ 0 by norm_num]
      apply Int.ModEq.pow
      exact h
    . rw [show (0 : ℤ)=1-1 by ring]
      refine Int.ModEq.sub ?_ (by exact h)
      rw [← one_pow 7]
      apply Int.ModEq.pow
      exact h
    . rw [show (0 : ℤ)=2-2 by ring]
      refine Int.ModEq.sub ?_ (by exact h)
      have := Int.ModEq.pow 7 <| show n ≡ 2 [ZMOD 3] by exact h
      apply Int.ModEq.trans this
      decide
--    3. **Divisibility by \(7\)**:
-- - We can check the values of \(n\) modulo \(7\):
-- - If \(n \equiv 0 \mod 7\), then \(n\) is divisible by \(7\).
-- - If \(n \equiv 1 \mod 7\), then \(n^{7} \equiv n \mod 7\) (by Fermat's Little Theorem), so \(n^{7} - n \equiv 0 \mod 7\).
-- - If \(n \equiv 2, 3, 4, 5, 6 \mod 7\), similar calculations show that \(n^{7} - n \equiv 0 \mod 7\) for these cases as well.
-- - Thus, \(n(n^{3} - 1)(n^{3} + 1)\) is divisible by \(7\).
  have h3 : n^7-n ≡ 0 [ZMOD 7] := by
    set p : ℕ := 7
    have hp : Nat.Prime p := by norm_num
    by_cases h : ↑p ∣ n
    . rw [← Int.modEq_zero_iff_dvd] at h
      have := Int.ModEq.pow p h
      rw [zero_pow (by linarith)] at this
      have := Int.ModEq.sub this h
      rwa [sub_zero] at this
    have hncp : IsCoprime n ↑p := by
      symm
      rw [Int.coprime_iff_nat_coprime]
      rw [Int.eq_natAbs_of_zero_le h₀.le] at h
      norm_cast at h
      rw [show p = (p : ℤ).natAbs from rfl] at h
      rwa [Nat.Prime.coprime_iff_not_dvd (by norm_cast)]
    -- Fermat's Little Theorem
    have := Int.ModEq.pow_card_sub_one_eq_one hp hncp
    replace := Int.ModEq.mul_right n this
    rw [one_mul, ← pow_succ, Nat.sub_add_cancel (by linarith)] at this
    replace := Int.ModEq.sub_right n this
    rwa [sub_self] at this
  -- Since \(n(n^{3} - 1)(n^{3} + 1)\) is divisible by \(2\), \(3\), and \(7\), we conclude that \(42\) divides \(n^{7} - n\) for all positive integers \(n\).
  have h12 : n^7-n ≡ 0 [ZMOD 2*3] := by
    rw [← Int.modEq_and_modEq_iff_modEq_mul (by decide)]
    exact ⟨h1, h2⟩
  rw [show (42 : ℤ) = 2*3*7 by norm_num]
  rw [← Int.modEq_and_modEq_iff_modEq_mul (by decide)]
  exact ⟨h12, h3⟩
