import Mathlib

open Set

/- a) when \( m \) is a prime number and \( 1 \leq q \leq m-1 \).-/
theorem number_theory_4771_1 {a : ℤ} {q m : ℕ} (hm : m.Prime) (hqpos : 0 < q) (hq : q < m) :
    SurjOn (fun j : ℤ => (a+j*q)%m) (Ico 0 m) (Ico 0 m) := by
--   To show that all memory locations are probed, we need to analyze the probing sequence \( h_{j}(K) \).

-- a) When \( m \) is prime and \( 1 \leq q \leq m-1 \):
-- 1. The initial hash value \( h(K) \) is computed as \( K \mod m \).
-- 2. The probing sequence is given by \( h_{j}(K) = (h(K) + j q) \mod m \).
-- 3. Since \( m \) is prime, the number \( q \) is coprime to \( m \) (as \( q \) is between 1 and \( m-1 \)).
-- 4. The sequence \( j q \mod m \) will generate all integers from \( 0 \) to \( m-1 \) as \( j \) varies from \( 1 \) to \( m-1 \) because multiplying by a number coprime to \( m \) ensures that we cover all residues modulo \( m \).
-- 5. Therefore, as \( j \) takes on values from \( 1 \) to \( m-1 \), \( h_{j}(K) \) will probe all memory locations from \( 0 \) to \( m-1 \).
  simp [SurjOn]
  intro x hx
  simp
  have : Nat.Coprime m q := by
    rcases hm.dvd_or_isRelPrime with (h : _ ∣ q) | h
    linarith [Nat.le_of_dvd hqpos h]
    rwa [Nat.coprime_iff_isRelPrime]
  obtain ⟨y, hy⟩ := Int.mod_coprime this.symm
  set z := ((x-a)*y) % m with hz
  use z
  constructor
  exact ⟨Int.emod_nonneg _ (by linarith), by apply Int.emod_lt_of_pos; linarith⟩
  have : x = x % m := by
    simp at hx
    symm
    apply Int.emod_eq_of_lt
    all_goals linarith
  rw [this]
  change _ ≡ _ [ZMOD _]
  apply Int.ModEq.add_left_cancel' (-a)
  rw [neg_add_cancel_left]
  have : z ≡ (x-a)*y [ZMOD m] := by simp [Int.ModEq, hz]
  have := Int.ModEq.mul_right q this
  apply Int.ModEq.trans this
  rw [mul_assoc, ← mul_one (-a+x)]
  apply Int.ModEq.mul
  . rw [sub_eq_add_neg, add_comm]
  . rw [mul_comm]; assumption

/- b) when \( m = 2^{r} \) and \( q \) is an odd number.-/
theorem number_theory_4771_2 {a : ℤ} {q m r : ℕ} (hq : Odd q) (hm : m = 2^r) (hr : 0 < r) :
    SurjOn (fun j : ℤ => (a+j*q)%m) (Ico 0 m) (Ico 0 m) := by
--    b) When \( m = 2^{r} \) and \( q \) is odd:
-- 1. Again, we start with the initial hash value \( h(K) = K \mod 2^{r} \).
-- 2. The probing sequence is \( h_{j}(K) = (h(K) + j q) \mod 2^{r} \).
-- 3. Since \( q \) is odd, it is coprime to \( 2^{r} \).
-- 4. The sequence \( j q \mod 2^{r} \) will also generate all integers from \( 0 \) to \( 2^{r}-1 \) as \( j \) varies from \( 1 \) to \( 2^{r}-1 \).
-- 5. This is because multiplying by an odd number ensures that we can reach every residue class modulo \( 2^{r} \).
-- 6. Thus, as \( j \) varies, \( h_{j}(K) \) will probe all memory locations from \( 0 \) to \( 2^{r}-1 \).
  simp [SurjOn]
  intro x hx
  simp
  have : Nat.Coprime m q := by
    rw [Nat.coprime_iff_gcd_eq_one]
    have : m.gcd q ∣ 2^r := by rw [← hm]; apply Nat.gcd_dvd_left
    rw [Nat.dvd_prime_pow Nat.prime_two] at this
    obtain ⟨k, hk⟩ := this
    cases' k with k
    exact hk.2
    have : ¬Odd q := by
      rw [Nat.not_odd_iff_even, even_iff_two_dvd]
      trans 2^(k+1)
      rw [pow_succ]
      . apply Nat.dvd_mul_left
      rw [← hk.2]
      apply Nat.gcd_dvd_right
    contradiction
  obtain ⟨y, hy⟩ := Int.mod_coprime this.symm
  set z := ((x-a)*y) % m with hz
  use z
  constructor; constructor
  . apply Int.emod_nonneg
    simp [hm]
  . apply Int.emod_lt_of_pos
    simp [hm]
  have : x = x % m := by
    simp at hx
    symm
    apply Int.emod_eq_of_lt
    all_goals linarith
  rw [this]
  change _ ≡ _ [ZMOD _]
  apply Int.ModEq.add_left_cancel' (-a)
  rw [neg_add_cancel_left]
  have : z ≡ (x-a)*y [ZMOD m] := by simp [Int.ModEq, hz]
  have := Int.ModEq.mul_right q this
  apply Int.ModEq.trans this
  rw [mul_assoc, ← mul_one (-a+x)]
  apply Int.ModEq.mul
  . rw [sub_eq_add_neg, add_comm]
  . rw [mul_comm]; assumption
