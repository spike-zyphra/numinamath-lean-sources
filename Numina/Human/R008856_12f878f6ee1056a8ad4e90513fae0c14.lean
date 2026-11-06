import Mathlib

/- 4.3. Find all functions $f: N \rightarrow N \cup\{0\}$ that satisfy the following conditions:

1) $f(m n)=f(m)+f(n)$ for all $m, n \in N$;
2) $f(10 m+3)=0$ for all $m \in N$;
3) $f(10)=0$. -/
theorem number_theory_104044 (f : ℕ → ℕ) :
    (∀ m n, m > 0 → n > 0 → f (m * n) = f m + f n) ∧
    (∀ m > 0, f (10 * m + 3) = 0) ∧
    f 10 = 0 → ∀ n > 0, f n = 0 := by
  intro ⟨hmul, h10, h0⟩
  -- Prove that f(1) = 0.
  have h1 : f 1 = 0 := by
    -- Observe that f(1) = f(1 * 1) = f(1) + f(1), so f(1) = 0.
    have := mul_one 1 ▸ hmul 1 1 zero_lt_one zero_lt_one
    omega
  -- Prove that f(x^n) = n * f(x) for all x > 0.
  have hpow {x n} (hx : x > 0) : f (x ^ n) = n * f x := by
    -- Proof by induction.
    induction n with
    -- f(x^0) = f(1) = 0 = 0 * f(x).
    | zero => simp [h1]
    | succ n ih =>
      -- f(x^(n + 1)) = f(x^n * x) = f(x^n) + f(x) = n * f(x) + f(x) = (n + 1) * f(x).
      rw [pow_succ, hmul _ _ (by positivity) hx, ih]
      group
  -- f(10) = 0 implies that 0 = f(2 * 5) = f(2) + f(5), so f(2) = f(5) = 0.
  have ⟨h2, h5⟩ : f 2 = 0 ∧ f 5 = 0 := by
    suffices f 10 = f 2 + f 5 by omega
    rw [← hmul _ _ (by norm_num) (by norm_num)]
  intro n hn
  -- Show that n > 0 can be written as
  -- n = 2^a * 5^b * k such that k and 2 are coprime, k and 5 are coprime, and k > 0.
  have ⟨k, a, b, h, hk2, hk5, hkpos⟩ : ∃ k a b, n = 2 ^ a * 5 ^ b * k ∧ k.Coprime 2 ∧ k.Coprime 5 ∧ k > 0 := by
    -- We have a general lemma. For any prime p and n > 0 we have:
    -- n = p ^ e * k such that k and p are coprime and k > 0.
    have hfactor {p n : ℕ} (hp : p.Prime) (h0 : n > 0) : ∃ k, n = p ^ n.factorization p * k ∧ k.Coprime p ∧ k > 0 := by
      use n / p ^ n.factorization p
      simp [Nat.ordProj_mul_ordCompl_eq_self, true_and]
      constructor
      · apply Nat.Coprime.symm
        exact Nat.coprime_ordCompl hp (ne_of_gt h0)
      constructor
      · apply Nat.pow_pos hp.pos
      · apply Nat.ordProj_le _ (by omega)
    -- Use the general lemma to find m such that
    -- n = 2^a * m, m and 2 are coprime, m > 0.
    have ⟨m, hnm, hm2, hm⟩ := hfactor Nat.prime_two hn
    -- Use the general lemma to find k such that
    -- m = 5^b * k, k and 5 are coprime, k > 0.
    have ⟨k, hmk, hk5, hk⟩ := hfactor Nat.prime_five hm
    use k, n.factorization 2, m.factorization 5
    nth_rw 1 [hnm, hmk, ← mul_assoc]
    simp only [hk, and_true, true_and]
    refine ⟨?_, hk5⟩
    -- It is left to show that k and 2 are coprime. This result follows
    -- from the facts that m and 2 are coprime and m = 5^b * k.
    rw [hmk] at hm2
    exact hm2.coprime_mul_left
  -- Show that k^4 ≡ 1 [MOD 10].
  have hk10 : k ^ 4 ≡ 1 [MOD 10] := by
    -- We have k ^ 4 ≡ 1 [MOD 2].
    replace hk2 : k ^ 4 ≡ 1 [MOD 2] := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      simp [← ZMod.natCast_eq_natCast_iff]
      -- k ^ 1 = 1 (mod 2) for any k ≠ 0.
      rw [← pow_one ((k : ZMod 2) ^ 4), ZMod.pow_card_sub_one_eq_one]
      -- Show that k ≠ 0 (mod 2).
      apply IsUnit.ne_zero
      apply IsUnit.pow
      -- k is coprime with 2, so k is a unit (mod 2) so k ≠ 0 (mod 2).
      rw [ZMod.isUnit_iff_coprime]
      exact hk2
    -- We have k ^ 4 ≡ 1 [MOD 5].
    replace hk5 : k ^ 4 ≡ 1 [MOD 5] := by
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      simp [← ZMod.natCast_eq_natCast_iff]
      -- k ^ 4 = 1 (mod 5) for any k ≠ 0 (it follows from Fermat's Little theorem).
      rw [ZMod.pow_card_sub_one_eq_one]
      -- Show that k ≠ 0 (mod 5).
      apply IsUnit.ne_zero
      -- k is coprime with 5, so k is a unit (mod 5) so k ≠ 0 (mod 5).
      rw [ZMod.isUnit_iff_coprime]
      exact hk5
    -- Use CRT to show that k ^ 4 ≡ 1 [MOD 2] and k ^ 4 ≡ 1 [MOD 5] implies k ^ 4 ≡ 1 [MOD 10].
    rw [show 10 = 2 * 5 by norm_num, ← Nat.modEq_and_modEq_iff_modEq_mul (by norm_num)]
    exact ⟨hk2, hk5⟩
  -- k ^ 4 ≡ 1 [MOD 10] implies that 3 k^4 ≡ 3 [MOD 10].
  -- So we can find q such that 3 k^4 = 10 q + 3.
  have ⟨q, hq⟩ : ∃ q, 3 * k ^ 4 = 10 * q + 3 := by
    have := hk10.mul_left 3
    use 3 * k ^ 4 / 10
    rw [Nat.ModEq.eq_1] at this
    norm_num at this
    nth_rw 3 [← this]
    rw [Nat.div_add_mod]
  -- Prove that f(k) = 0.
  have hk : f k = 0 := by
    -- Consider two cases: k = 1 or k ≥ 2.
    cases' show k = 1 ∨ k ≥ 2 by omega with hk hk
    -- If k = 1 then f(k) = f(1) = 0.
    · rw [hk, h1]
    -- If k ≥ 2 then f(k) = 0 follows from f(3 k ^ 4) = 0
    -- (because 0 = f(3 k^4) = f(3) + f(k^4) = f(3) + 4 f(k) implies f(k) = 0).
    · suffices h : f (3 * k ^ 4) = 0 by
        rw [hmul _ _ (by norm_num) (by positivity), hpow hkpos] at h
        omega
      -- We have f(3 k ^ 4) = f(10 q + 3) for some q.
      rw [hq, h10]
      -- f(10 q + 3) = 0 for all q > 0. It is left to show that q > 0.
      -- Suppose that q = 0 and show that 3 k ^ 4 > 10 q + 3 = 3.
      contrapose! hq
      apply ne_of_gt
      -- The result follows from k ≥ 2, k ^ 4 ≥ 16.
      suffices k ^ 4 ≥ 2 ^ 4 by linarith
      apply Nat.pow_le_pow_left hk
  -- We have f(k) = 0, f(2) = 0, f(5) = 0 and n = 2^a * 5^b * k.
  -- We get f(n) = a f(2) + b f(5) + f(k) = 0.
  rw [h, hmul _ _ (by positivity) hkpos, hmul _ _ (by positivity) (by positivity)]
  rw [hpow (by norm_num), hpow (by norm_num), h2, h5, hk]
  norm_num