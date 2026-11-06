import Mathlib

/- Show that if \( n \) is odd and \( 3 \nmid n \), then \( n^{2} \equiv 1 \pmod{24} \).-/
theorem number_theory_4788 (n : ℕ) (h₀ : Odd n) (h₁ : ¬ 3 ∣ n) :
    n^2 ≡ 1 [MOD 24] := by
--    2. **Calculating \( n^2 \)**: We start by calculating \( n^2 \):
-- \[
-- n^2 = (2k + 1)^2 = 4k^2 + 4k + 1 = 4k(k + 1) + 1.
-- \]
-- Since \( k(k + 1) \) is always even (the product of two consecutive integers), we can denote it as \( 2m \) for some integer \( m \):
-- \[
-- n^2 = 8m + 1.
-- \]
-- 3. **Finding \( n^2 \mod 8 \)**: From the expression \( n^2 = 8m + 1 \), we see that:
-- \[
-- n^2 \equiv 1 \pmod{8}.
-- \]
  have h1 : n^2 ≡ 1 [MOD 8] := by
    suffices ∃ m, n^2 = 8*m + 1 by
      obtain ⟨m, hm⟩ := this
      rw [hm]
      rw [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
      simp
    obtain ⟨k, hk⟩ := h₀
    have : 8 ∣ 4*k*(k+1) := by
      rw [show 8 = 4*2 by norm_num, mul_assoc]
      apply Nat.mul_dvd_mul_left
      rw [← even_iff_two_dvd]
      exact Nat.even_mul_succ_self k
    obtain ⟨m, hm⟩ := this
    use m
    rw [hk, ← hm]
    ring
--    4. **Finding \( n^2 \mod 3 \)**: Next, we consider \( n \mod 3 \). Since \( n \) is odd and not divisible by 3, the possible residues of \( n \mod 3 \) are 1 or 2:
-- - If \( n \equiv 1 \pmod{3} \), then:
-- \[
-- n^2 \equiv 1^2 \equiv 1 \pmod{3}.
-- \]
-- - If \( n \equiv 2 \pmod{3} \), then:
-- \[
-- n^2 \equiv 2^2 \equiv 4 \equiv 1 \pmod{3}.
-- \]
-- In both cases, we find that:
-- \[
-- n^2 \equiv 1 \pmod{3}.
-- \]
  have h2 : n^2 ≡ 1 [MOD 3] := by
    rw [Nat.ModEq, pow_two, Nat.mul_mod]
    rw [Nat.dvd_iff_mod_eq_zero] at h₁
    have : n % 3 < 3 := by apply Nat.mod_lt; norm_num
    interval_cases (n % 3)
    . contradiction
    . simp
    . simp
--    5. **Combining results using the Chinese Remainder Theorem**: We have established:
-- \[
-- n^2 \equiv 1 \pmod{8}
-- \]
-- and
-- \[
-- n^2 \equiv 1 \pmod{3}.
-- \]
-- Since 8 and 3 are coprime, we can combine these results. By the Chinese Remainder Theorem, there is a unique solution modulo \( 24 \) (since \( 24 = 8 \times 3 \)).
  rw [show 24 = 8 * 3 by norm_num]
  rw [← Nat.modEq_and_modEq_iff_modEq_mul <|
    show Nat.Coprime 8 3 by decide]
  exact ⟨h1, h2⟩
