import Mathlib

/- For which integers $n \in\{1,2, \ldots, 15\}$ is $n^{n}+1$ a prime number?-/
theorem number_theory_609496 :
    {n : ℕ | n ∈ Finset.Icc 1 15 ∧ Nat.Prime (n ^ n + 1)} = {1, 2, 4} := by
  -- Simplify the goal into two parts.
  ext n
  simp
  apply Iff.intro
  . -- First show that if n ∈ {1, ..., 15} and n ^ n + 1 is a prime, then n = 1, 2 or 4.
    rintro ⟨⟨h₀, h₁⟩, h₂⟩
    -- Show that n cannot have odd prime factor. In other words, any prime that divides n must be 2.
    have h₃ {p : ℕ} : Nat.Prime p → p ∣ n → p = 2 := by
      intro hp hp'
      -- Suppose on the contrary that some prime p ≠ 2 divides n.
      by_contra!
      -- It suffices to show that p cannot be odd.
      apply Nat.Prime.odd_of_ne_two hp at this
      have hp'' := hp'
      rw [dvd_iff_exists_eq_mul_left] at hp'
      -- Let c = n / p.
      obtain ⟨c, hp'⟩ := hp'
      -- Show that n ^ (n / p) + 1 ∣ n ^ n + 1, so n ^ n + 1 is composite.
      have h₄ : n ^ c + 1 ∣ n ^ n + 1 := by
        calc
          _ ∣ (n ^ c) ^ p + 1 ^ p := Odd.nat_add_dvd_pow_add_pow _ _ this
          _ = n ^ n + 1 := by
            rw [<-Nat.pow_mul, <-hp']
            simp
      rw [dvd_iff_exists_eq_mul_right] at h₄
      obtain ⟨k, h₄⟩ := h₄
      -- Now n ^ n + 1 = (n ^ c + 1) * k, but k ≠ 1.
      have h₅ : k ≠ 1 := by
        -- This is because if k = 1, then n ^ n + 1 = n ^ c + 1, which implies n ^ n = n ^ c, which is impossible.
        by_contra!
        simp [this] at h₄
        apply Nat.pow_right_injective at h₄
        . -- We have n = c, which is impossible since otherwise p = 1.
          simp [h₄, show c ≠ 0 by omega] at hp'
          norm_num [hp'] at hp
        . -- Verify that 2 ∣ n.
          calc
            2 ≤ p := Nat.Prime.two_le hp
            _ ≤ n := Nat.le_of_dvd (show 0 < n by omega) hp''
      -- Now we derive a contradiction that a composite number is a prime.
      rw [h₄] at h₂
      absurd h₂
      apply Nat.not_prime_mul _ h₅
      . -- Verify that n ^ c + 1 ≠ 1.
        simp
        omega
    replace h₃ := Nat.eq_prime_pow_of_unique_prime_dvd (show n ≠ 0 by positivity) h₃
    -- Let k = n.primeFactorsList.length.
    let k := n.primeFactorsList.length
    rw [show n.primeFactorsList.length = k by rfl] at h₃
    -- Show that k < 4.
    have h₄ : 2 ^ k < 2 ^ 4 := by
      simp [<-h₃]
      omega
    rw [Nat.pow_lt_pow_iff_right (by norm_num)] at h₄
    -- Consider possible values of k.
    interval_cases k
    . -- If k = 0, we get n = 1, one of the solutions.
      tauto
    . -- If k = 1, we get n = 2, one of the solutions.
      tauto
    . -- If k = 2, we get n = 4, one of the solutions.
      tauto
    . -- If k = 3, we get n = 8, which is not a solution by direct checking.
      norm_num [h₃] at h₂
  . -- Now check that for n = 1, 2 and 4, we indeed have n ^ n + 1 being prime.
    rintro (rfl | rfl | rfl)
    . -- Case n = 1.
      norm_num
    . -- Case n = 2.
      norm_num
    . -- Case n = 4.
      norm_num
