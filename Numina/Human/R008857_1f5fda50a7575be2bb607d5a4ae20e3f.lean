import Mathlib  

/-For a positive integer $k$, let $d(k)$ denote the number of divisors of $k$ (e.g. $d(12)=6$ ) and let $s(k)$ denote the digit sum of $k$ (e.g. $s(12)=3$ ). A positive integer $n$ is said to be amusing if there exists a positive integer $k$ such that $d(k)=s(k)=n$. What is the smallest amusing odd integer greater than 1 ?-/
theorem number_theory_604208 : 
  let amusing := fun n => ∃ k, 0 < k ∧ k.divisors.card = n ∧ (Nat.digits 10 k).sum = n;
  IsLeast {n | Odd n ∧ n > 1 ∧ amusing n} 9 := by
    constructor 
    · -- To see that 9 is amusing, note that $d(36)=s(36)=9$.
      simp 
      refine ⟨by decide, ⟨36, by omega, by decide, ?_⟩ ⟩ 
      suffices (Nat.digits 10 36) = [6,3] by simp
      simp 
    · simp [lowerBounds]
      intro a odda age1 k kpos hk1 hk2 
      by_contra! hcon
      -- The auxiliary lemma states that for all positive integers $a$, if $a>1$, d(a) is odd and d(a) ≤ 7, a is a prime power.
      have l2 (x : ℕ) (hx : x ≠ 0) (xne1 : x ≠ 1) (h1 : Odd (x.divisors.card)) (h2 : x.divisors.card ≤ 7) :
        ∃ p, Nat.Prime p ∧ x = p^(x.divisors.card - 1) := by
          rw [Nat.card_divisors hx] at h1 
          have h3 : ∀ y ∈ x.primeFactors, Even (Nat.factorization x y) := by 
            intro y hy 
            by_contra! hcon
            simp at hcon
            have : ∏ x_1 ∈ x.primeFactors, (x.factorization x_1 + 1) = (x.factorization y + 1) * ∏ x_2 ∈ (x.primeFactors \ {y}), (x.factorization x_2 + 1):= 
              Finset.prod_eq_mul_prod_diff_singleton hy fun x_1 => x.factorization x_1 + 1
            have : Even (∏ x_1 ∈ x.primeFactors, (x.factorization x_1 + 1)) := by 
              simp [this]; apply Even.mul_right; simp [hcon] 
            exact Nat.not_odd_iff_even.mpr this h1
          have h4 : ∀ y ∈ x.primeFactors, 2 ≤ Nat.factorization x y := by 
            intro y hy 
            have : x.factorization y  ≠  0 := by 
              intro hcon
              rw [Nat.factorization_eq_zero_iff] at hcon 
              simp at hy
              tauto
            have : x.factorization y ≠ 1 := by 
              have := h3 y hy; exact fun fact1 => by simp [fact1] at this 
            omega 
          have h5 : x.primeFactors.card = 1 := by 
            have : x.primeFactors ≠ ∅ := by simp; tauto
            replace this : x.primeFactors.card ≠ 0 := by simp [this]
            by_contra! hc 
            replace hc : 2 ≤ x.primeFactors.card := by omega
            obtain ⟨s, hss, cards⟩ := Finset.exists_subset_card_eq hc
            rw [Finset.card_eq_two] at cards
            obtain ⟨y, z, ynez, spair⟩ := cards 
            have ymem : y ∈ x.primeFactors := hss (by simp [spair])
            have zmem : z ∈ x.primeFactors := hss (by simp [spair])
            have yadic := h4 y ymem 
            have zadic := h4 z zmem
            simp at ymem zmem
            have y2coprimez2 := Nat.coprime_pow_primes 2 2 ymem.1 zmem.1 ynez
            have ⟨u, hu⟩ : y^2 * z^2 ∣ x:= by 
              have hy2 : y^2 ∣ x := (Nat.Prime.pow_dvd_iff_dvd_ordProj ymem.1 hx).mpr (pow_dvd_pow _ yadic)
              have hz2 : z^2 ∣ x := (Nat.Prime.pow_dvd_iff_dvd_ordProj zmem.1 hx).mpr (pow_dvd_pow _ zadic)
              exact Nat.Coprime.mul_dvd_of_dvd_of_dvd y2coprimez2 hy2 hz2
            have : (y^2 * z^2).divisors.card ≤ x.divisors.card := by 
              suffices (y ^ 2 * z ^ 2).divisors ⊆ x.divisors from Finset.card_le_card this
              exact Nat.divisors_subset_of_dvd hx (by simp [hu])
            have card_divsors_prime_sq {p : ℕ} (hp : Nat.Prime p): (p^2).divisors.card = 3 := by
              rw [Nat.divisors_prime_pow]; simp; exact hp
            rw [Nat.Coprime.card_divisors_mul] at this
            rw [card_divsors_prime_sq ymem.1, card_divsors_prime_sq zmem.1] at this
            linarith
            exact Nat.coprime_pow_primes 2 2 ymem.1 zmem.1 ynez
          rw [←isPrimePow_iff_card_primeFactors_eq_one] at h5
          obtain ⟨p, k, h⟩ := h5
          nth_rw 2 [← h.2.2]
          rw [Nat.divisors_prime_pow (Nat.prime_iff.2 h.1)]
          simp [Nat.Prime.factorization_pow]
          exact ⟨p, Nat.prime_iff.2 h.1, h.2.2.symm⟩ 
      -- show that $p^{2} \equiv 3(\bmod 9)$ is impossible
      have pow2mod9not3 (p : ℕ) : ¬ p^2 ≡ 3 [MOD 9] := by 
        mod_cases p % 9 <;> replace H := Nat.ModEq.pow 2 H <;> intro H' 
        <;> have := H'.symm.trans H <;> tauto
      -- show that $p^{4} \equiv 5(\bmod 9)$ is impossible.
      have pow4mod9not5 (p : ℕ) : ¬ p^4 ≡ 5 [MOD 9] := by 
        mod_cases p % 9 <;> replace H := Nat.ModEq.pow 4 H <;> intro H' 
        <;> have := H'.symm.trans H <;> tauto 
      -- show that $p^{6} \equiv 7(\bmod 9)$ is impossible. 
      have pow6mod9not7 (p : ℕ) : ¬ p^6 ≡ 7 [MOD 9] := by 
        mod_cases p % 9 <;> replace H := Nat.ModEq.pow 6 H <;> intro H' 
        <;> have := H'.symm.trans H <;> tauto 
      -- When $a < 9$, a is not amusing.
      interval_cases a <;> try tauto 
      all_goals have := hk2 ▸ Nat.modEq_nine_digits_sum k
      all_goals obtain ⟨p, pp, hpow⟩ := l2 k (by omega) (fun k1 => by norm_num [k1] at this; tauto) (by simp [hk1]; decide) (by linarith)
      all_goals (rw [hk1] at hpow; simp [hpow] at this)
      all_goals tauto



    
