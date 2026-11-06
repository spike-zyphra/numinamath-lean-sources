import Mathlib

/- Find the largest prime divisor of $25^2+72^2$. -/
theorem algebra_13275 : IsGreatest {p | Nat.Prime p ∧ p ∣ (25^2 + 72^2)} 157 := by
  -- Sophie Germain identity. a^4+b^4=(a^2+2b^2+2ab)(a^2+2b^2-2ab)
  have lemma_S_G' (a b:ℤ): a^4 + 4*b^4 =
    (a^2+2*b^2+2*a*b) * (a^2+2*b^2-2*a*b) := by ring
  have lemma_S_G (a b:ℕ): a^4 + 4*b^4 =
    (a^2+2*b^2+2*a*b) * (a^2+2*b^2-2*a*b) := by
      apply Int.ofNat_inj.mp; simp
      rw [lemma_S_G']
      simp
      left
      have: 2*a*b ≤ a^2+2*b^2 := by
        apply Int.ofNat_le.mp; simp
        have: a^2+2*b^2-(2*a*b:ℤ) ≥ 0 := by
          have hh1: a^2+2*b^2-(2*a*b:ℤ) = b^2 + (a-b)^2 := by ring
          have hh2 := sq_nonneg (b:ℤ)
          have hh3 := sq_nonneg (a-b:ℤ)
          rw [hh1]; linarith [hh2,hh3]
        exact Int.le_of_sub_nonneg this
      simp [this]
  -- notice that 25=5^2 and 72 = 2 x 36 = 2 x 6^2, so 25^2+72^2 = 5^4 + 4 x 6^2. and we can use Sophie Germain identity to simplify.
  have h1: 25^2+72^2 = 157 * 37 := by
    have ht1: 25^2 = 5^4 := by norm_num
    have ht2: 72^2 = 4 * 6^4 := by norm_num
    rw [ht1, ht2, lemma_S_G]
    -- 5^2+2x6^2+2x5x6 = 25 + 72 + 60 = 97+60 = 157
    have ht3: 5^2+2*6^2+2*5*6 = 157 := by norm_num
    -- 5^2+2x6^2-2x5x6 = 25+72-60 = 97-60=37
    have ht4: 5^2+2*6^2-2*5*6 = 37 := by norm_num
    rw [ht3, ht4]
  -- since 157 and 37 are both primes, we immediately get the answer. following lemma says, if p ∣ p1 * p2, then p can only be p1 or p2.
  have lemma_pdvd(p p1 p2:ℕ)(hp: Nat.Prime p)(hp1: Nat.Prime p1) (hp2: Nat.Prime p2): p ∣ p1*p2 → p = p1 ∨ p = p2 := by
    intro h
    have dvdor: p ∣ p1 ∨ p ∣ p2 := (Nat.Prime.dvd_mul hp).mp h
    rcases dvdor with dp1 | dp2
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp hp1).mp dp1
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp hp2).mp dp2
  rw [h1]
  rw [IsGreatest, upperBounds]; simp
  constructor
    -- first direction, we verify 157 satisfy the condition.
  · norm_num
    -- and the second direction, we prove any prime number divide 5809, that number must ≤ 157. we use lemma_pdvd
  · intro p pp pdvd
    have ht1: 5809 = 157 * 37 := by norm_num
    have ht2: Nat.Prime 157 := by norm_num
    have ht3: Nat.Prime 37 := by norm_num
    rw [ht1] at pdvd
    have peq := lemma_pdvd p 157 37 pp ht2 ht3 pdvd
    rcases peq with hhp | hhp <;> rw [hhp]; norm_num