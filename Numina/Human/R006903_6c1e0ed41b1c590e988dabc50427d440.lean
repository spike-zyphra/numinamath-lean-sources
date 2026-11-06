import Mathlib

/- Prove that any irreducible fraction $\frac{p}{q}$, where $p$ and $q$ are positive integers and $q$ is odd, is equal to a fraction $\frac{n}{2^{k}-1}$ for some positive integers $n$ and $k$. -/
theorem number_theory_241332 {p q : ℕ} (hp : 0 < p) (hq : Odd q)
    (h : Nat.Coprime p q) :
    ∃ n k : ℕ, 0 < n ∧ 0 < k ∧ (p / q : ℚ) = n / (2 ^ k - 1) := by
  -- show Coprime 2 q
  have Coprime2q : Nat.Coprime 2 q := by
    apply Odd.coprime_two_left
    exact hq
  clear h

  -- show that q ∣ 2 ^ q.totient - 1
  apply Nat.ModEq.pow_totient at Coprime2q
  symm at Coprime2q
  apply Nat.ModEq.dvd at Coprime2q

  -- exchange the type of q ∣ 2 ^ q.totient - 1
  have type : (2 ^ q.totient - 1 : ℕ) = ((2 ^ q.totient : ℕ) - (1 : ℕ) : ℤ) := by
    apply Int.natCast_sub
    apply Nat.one_le_two_pow

  rw [<-type] at Coprime2q
  norm_cast at Coprime2q

  -- so that we have k ∶ ℕ
  obtain ⟨k, hk⟩ := Coprime2q

  use (k * p)
  use (q.totient)
  -- show that 0 < q.totient
  have pos_qt : 0 < q.totient := by
    contrapose! hq
    rw [Nat.le_zero_eq] at hq
    rw [Nat.totient_eq_zero] at hq
    rw [hq]
    simp
  -- show that 0 < k
  have pos_k : 0 < k := by
    contrapose! hk
    rw [Nat.le_zero_eq] at hk
    rw [hk]
    simp
    -- show that 2 ^ q.totient - 1 > 0
    have pos_pow : 0 < 2 ^ q.totient - 1 := by
      -- show that 1 < 2 ^ q.totient
      have h : 2 ^ 0 < 2 ^ q.totient := by
        apply Nat.pow_lt_pow_of_lt
        norm_num
        exact pos_qt
      ring_nf at h
      apply Nat.sub_pos_of_lt
      exact h
    -- easily check
    linarith only [pos_pow]
  -- show that 0 < q
  replace hq : 0 < q := by
    contrapose! hq
    rw [Nat.le_zero_eq] at hq
    rw [hq]
    simp
  -- finally show that p / q = n / (2 ^ k - 1)
  simp [hp, pos_k, pos_qt]
  zify at hk
  rw [type] at hk
  rify at hk pos_k ⊢
  rw [hk]
  field_simp
  ring_nf
