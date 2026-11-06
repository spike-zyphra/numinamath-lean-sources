import Mathlib

-- If 0 < n and (n - 1) % 100 = r then n % 100 = (r + 1) % 100.
lemma lemma_1 {n r : ℕ} (hn : 0 < n) (hn1 : (n - 1) % 100 = r) : n % 100 = (r + 1) % 100 := by
  -- We have r < 100 (because r = (n - 1) % 100).
  have hr : r < 100 := by
    rw [← hn1]
    apply Nat.mod_lt
    norm_num
  -- (n - 1) % 100 = r is equivalent to n - 1 ≡ r [MOD 100].
  rw [← Nat.mod_eq_of_lt hr, ← Nat.ModEq.eq_1] at hn1
  -- n % 100 ≡ (r + 1) % 100 is equivalent to n ≡ r + 1 [MOD 100].
  rw [← Nat.ModEq.eq_1]
  -- We get the following equalities (mod 100):
  -- n - 1 = r (mod 100) and n = r + 1 (mod 100).
  rw [← ZMod.eq_iff_modEq_nat] at hn1 ⊢
  push_cast [hn] at hn1 ⊢
  -- n - 1 = r (mod 100) implies n = r + 1 (mod 100).
  linear_combination hn1

-- If 5 does not divide n then 25 divides n^20 - 1.
lemma lemma_2 {n : ℕ} (hn : ¬ 5 ∣ n) : 25 ∣ n^20 - 1 := by
  -- We have 0 < n^k (because ¬ 5 ∣ n).
  have hn0 k : 0 < n^k := by
    suffices 0 < n by simp [this]
    contrapose! hn
    simp [show n = 0 by omega]
  -- Show that n^4 = 1 (mod 5).
  have h5 : (n : ZMod 5) ^ 4 = 1 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    -- Fermat's Little Theorem implies that n^4 = 1 (mod 5) for all n ≠ 0 (mod 5).
    apply ZMod.pow_card_sub_one_eq_one
    -- Show that n is a unit (mod 5), so n ≠ 0 (mod 5).
    apply IsUnit.ne_zero
    -- It is enough to show that n is coprime with 5.
    rw [ZMod.isUnit_iff_coprime, Nat.coprime_comm]
    -- ¬ 5 ∣ n so 5 and n a re coprime.
    rw [Nat.prime_five.coprime_iff_not_dvd]
    exact hn
  -- We have n^20 - 1 = (n^4 - 1) * ((n^4)^4 + (n^4)^3 + (n^4)^2 + n^4 + 1).
  have eq : n^20 - 1 = (n^4 - 1) * ((n^4)^4 + (n^4)^3 + (n^4)^2 + n^4 + 1) := by
    zify [hn0]
    ring
  rw [eq, show 25 = 5 * 5 by norm_num]
  -- Show that 5 ∣ n^4 - 1 and 5 ∣ (n^4)^4 + (n^4)^3 + (n^4)^2 + n^4 + 1.
  -- We get the following equalities (mod 5):
  -- n^4 - 1 = 0 (mod 5) and (n^4)^4 + (n^4)^3 + (n^4)^2 + n^4 + 1 = 0 (mod 5).
  -- These results follow from n^4 = 1 (mod 5).
  apply Nat.mul_dvd_mul <;> rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  · simp [hn0, h5]
  · simp [h5]
    reduce_mod_char

-- If 25 divides n and n is odd then n % 100 = 25 or n % 100 = 75.
lemma lemma_3 {n : ℕ} (hn : 25 ∣ n) (h : Odd n) : n % 100 = 25 ∨ n % 100 = 75 := by
  -- We have n = 25 * k for some k ∈ ℕ.
  have ⟨k, hk⟩ := hn
  -- We have k = 4 * (k / 4) + k % 4, so we get
  -- n = 100 * (k / 4) + 25 * (k % 4).
  rw [← Nat.div_add_mod k 4, mul_add, ← mul_assoc, show 25 * 4 = 100 by norm_num] at hk
  -- We get n % 100 = 25 * (k % 4).
  rw [hk, Nat.mul_add_mod]
  have hk4 : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  -- Consider all possible values of k % 4.
  -- If k % 4 = 1 then n % 100 = 25, if k % 4 = 3 then n % 100 = 75.
  interval_cases k % 4 <;> norm_num <;> contrapose! h <;> simp [hk]
  · -- If k % 4 = 0 then n = 100 * (k / 4), so n is not odd.
    apply Even.mul_right
    decide
  · -- If k % 4 = 2 then n = 100 * (k / 4) + 50, so n is not odd.
    apply Even.add _ (by decide)
    apply Even.mul_right
    decide

-- If n is even then n^20 % 100 % 4 = 0.
lemma lemma_4 {n : ℕ} (h : Even n) : n^20 % 100 % 4 = 0 := by
  -- We have n = 2 * k for some k ∈ ℕ.
  have ⟨k, hk⟩ := even_iff_exists_two_mul.mp h
  -- n^20 % 100 % 4 = n^20 % 4 = k^20 * 2^20 % 4 = 0.
  rw [Nat.mod_mod_of_dvd _ (by norm_num), hk, mul_comm, mul_pow, Nat.mul_mod]
  norm_num

/- 8,9
Let $N$ be an even number that is not divisible by 10. Find the tens digit of the number $N^{20}$. -/
theorem number_theory_192459 (N : ℕ) (h₀ : Even N) (h₁ : ¬10 ∣ N) :
    (Nat.digits 10 (N^20))[1]! = 7 := by
  -- Show that 2 ≤ N.
  have hn2 : 2 ≤ N := by
    -- N is even, so N = 2 * k.
    have ⟨k, hk⟩ := even_iff_exists_two_mul.mp h₀
    rw [hk]
    -- It is enough to show that k ≠ 0.
    suffices k ≠ 0 by omega
    -- Assume that k = 0 and show that 10 ∣ N.
    -- k = 0 implies that N = 0, so 10 ∣ N.
    contrapose! h₁
    simp [hk, h₁]
  -- We have 100 < 2^20 ≤ N^20.
  have hn20 : 100 < N^20 := by
    apply lt_of_lt_of_le (show 100 < 2^20 by norm_num)
    apply pow_le_pow hn2 (by linarith) (le_refl _)
  -- It is enough to show that (N^20 - 1) % 100 = 75.
  suffices h : (N^20 - 1) % 100 = 75 by
    -- lemma_1 implies that N^20 % 100 = 76.
    replace h : N^20 % 100 = 76 := by rw [lemma_1 (by linarith) h]
    -- Expand the definitions of Nat.digits.
    rw [Nat.digits_def' (by norm_num) (by linarith)]
    rw [Nat.digits_def' (by norm_num) (by omega)]
    simp
    -- We get the following goal:
    -- N ^ 20 / 10 % 10 = 7.
    -- We have N^20 = 100 * (N^20 / 100) + N^20 % 100.
    rw [← Nat.div_add_mod (N^20) 100, h, show 100 = 10 * 10 by norm_num, mul_assoc]
    -- So N^20 / 10 % 10 = (N^20 % 100 / 10) % 10 = 76 / 10 % 10 = 7.
    rw [Nat.mul_add_div (by norm_num), Nat.mul_add_mod]
  -- N^20 is even (because N is even).
  have heven : Even (N ^ 20) := by simp [Nat.even_pow, h₀]
  -- N^20 - 1 is odd (because 0 < N^20 is even).
  have hodd : Odd (N ^ 20 - 1) := by
    apply Nat.Even.sub_odd (by linarith) heven odd_one
  -- 5 does not divide N (because 10 does not divide n and 10 = 2 * 5).
  have hdvd : ¬ 5 ∣ N := by
    contrapose! h₁
    rw [show 10 = 2 * 5 by norm_num]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) _ h₁
    rwa [← even_iff_two_dvd]
  -- lemma_2 implies that 25 ∣ N^20 - 1.
  -- lemma_3 implies that (N^20 - 1) % 100 = 25 or (N^20 - 1) % 100 = 75.
  have h := lemma_3 (lemma_2 hdvd) hodd
  cases' h with h h
  · -- If (N^20 - 1) % 100 = 25 then lemma_1 implies that N^20 % 100 = 26.
    have eq := lemma_1 (by linarith) h
    -- N is even so lemma_4 implies that N^20 % 100 % 4 = 0 but
    -- 26 % 4 ≠ 0, so this case is impossible.
    have := lemma_4 h₀
    norm_num [eq] at this
  · -- If (N^20 - 1) % 100 = 75 then we are done.
    exact h