import Mathlib
set_option maxRecDepth 1000

/-Find the smallest composite number that has no prime factors less than 10.-/
theorem algebra_12272 :
    IsLeast {n > 1 | ¬Nat.Prime n ∧ ∀ p, p.Prime → p < 10 → ¬p ∣ n} 121 := by
  have : ∃s, s = {n > 1 | ¬Nat.Prime n ∧ ∀ p, p.Prime → p < 10 → ¬p ∣ n} := by simp
  rcases this with ⟨s, hs⟩
  rw [hs.symm]
  -- A composite number is the product of two smaller natural numbers.  If a composite has no prime divisors less than 10, then the smallest that product can be is $11 \cdot 11 = \boxed{121}$.
  unfold IsLeast
  have _121_in_s : 121 ∈ s := by
    rw [hs]
    simp
    constructor
    . -- 121 is not prime
      exact of_decide_eq_false rfl
    . -- ∀ (p : ℕ), Nat.Prime p → p < 10 → ¬p ∣ 121
      intro p p_prime p_lt_10
      have : 121 = 11 * 11 := by linarith
      rw [this]
      have : ¬p ∣ 11 := by
        apply (Nat.Prime.coprime_iff_not_dvd p_prime).mp
        apply (Nat.coprime_primes (by norm_cast) (by norm_cast)).mpr
        linarith
      apply Nat.Prime.not_dvd_mul p_prime
      repeat exact this
  use _121_in_s
  refine (le_csInf_iff' ?intro.right.hs).mp ?intro.right.a
  exact Set.nonempty_of_mem _121_in_s
  apply le_csInf
  exact Set.nonempty_of_mem _121_in_s
  intro b hb
  rw [hs] at hb
  simp at hb
  rcases hb with ⟨one_lt_b, b_not_prime, hb_prime⟩
  have hb_prime: ¬2 ∣ b ∧ ¬3 ∣ b ∧ ¬5 ∣ b ∧ ¬7 ∣ b := by
    use hb_prime 2 (by norm_cast) (by norm_cast)
    use hb_prime 3 (by norm_cast) (by norm_cast)
    use hb_prime 5 (by norm_cast) (by norm_cast)
    use hb_prime 7 (by norm_cast) (by norm_cast)
  -- hmmm, We cannot avoid exhaustive search, because, we had listed it in subconsciousness
  -- Although we were completely unaware
  have not_found : ¬∃a<121, (a > 1 ∧ ¬Nat.Prime a ∧  ¬2 ∣ a ∧ ¬3 ∣ a ∧ ¬5 ∣ a ∧ ¬7 ∣ a) := by
    decide
  simp at not_found hb_prime
  by_contra!
  specialize not_found b this one_lt_b b_not_prime hb_prime.1 hb_prime.2.1 hb_prime.2.2.1
  absurd hb_prime.2.2.2
  exact not_found
