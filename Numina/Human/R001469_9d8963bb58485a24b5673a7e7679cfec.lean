import Mathlib

@[simp]
theorem ofNat_toNat (a : Int) : (a.toNat : Int) = max a 0 := by
  match a with
  | Int.ofNat n => simp
  | Int.negSucc n => aesop

set_option maxHeartbeats 800000
/- All integers $m \geq 2$ such that every $n$ with $\frac{m}{3} \leq n \leq \frac{m}{2}$ divides the binomial coefficient $\left(\begin{array}{c}n \\ m-2 n\end{array}\right)$ are prime numbers. -/
theorem number_theorey_4 :
  {(m : ℤ)| (m ≥ 2) ∧ ∀(n : ℕ), ((m / 3 : ℚ) ≤ n ∧ n ≤ (m / 2 : ℚ)) → n ∣ n.choose (m.toNat - 2 * n)} =
  {(m : ℤ)| ∃ x, Nat.Prime x ∧ x = m} := by
  rw [Set.Subset.antisymm_iff]
  constructor
  -- Prove that all numbers that satisfy the requirements of the question are prime numbers.
  · intro m hm
    simp at hm ⊢
    use m.toNat
    constructor
    · obtain ⟨hm, h⟩ := hm
      -- If $m = 2$, then $m$ is prime.
      by_cases h₀ : m = 2
      · rw [h₀]
        exact Nat.prime_two
      -- If $m > 2$, then assume $m$ is not a prime number and find a contradiction.
      · by_contra! h1
        -- If $m > 2$, then m.toNat > 2.
        have hm₀ : m.toNat > 2 := by
          simp
          by_contra h
          simp at h
          apply h₀
          linarith
        -- m.toNat is either an even number greater than 2, or has an odd prime factor that is not equal to itself.
        have h2 : (∃ k > 1, m.toNat = 2 * k) ∨ ∃ p, Nat.Prime p ∧ p > 2 ∧ ∃ (k : ℕ), m.toNat = p * (2 * k + 3) := by
          -- If m.toNat is not prime, then there is a prime factor $p$ with $p ≥ 2$ and $p$ < m.toNat.
          rw [Nat.not_prime_iff_exists_dvd_lt (by linarith)] at h1
          · by_cases hm' : Even m.toNat
            -- While m.toNat is an even number, it is certainly an even number greater than 2.
            · left
              rw [Even] at hm'
              obtain ⟨k, hk⟩ := hm'
              use k
              constructor
              · linarith
              · rw [hk]
                omega
            -- While m.toNat is an odd number, it has an odd prime factor $p$ and there exists an odd number $l \leq 3$ such that m.toNat = $pl$.
            · right
              obtain ⟨p, hp, hp1, hp2⟩ := h1
              -- choose the smallest prime factor $p1$ of $p$.
              let p1 := p.primeFactorsList.head (by simp [Nat.primeFactorsList_eq_nil]; omega)
              have p1' : Nat.Prime p1 := by
                apply Nat.prime_of_mem_primeFactorsList (n := p)
                simp [p1]
              -- The odd prime factor $p$ which exactly we want is $p1$.
              use p1
              refine ⟨p1', ?_, ?_⟩
              · by_contra! h
                have : p1 = 2 := by linarith [Nat.Prime.two_le p1']
                suffices Even m.toNat by tauto
                refine Even.trans_dvd ?_ hp
                refine Even.trans_dvd ?_ (Nat.dvd_of_mem_primeFactorsList (n := p) (p := p1) (by simp [p1]))
                exact (Nat.Prime.even_iff p1').mpr this
              -- To show there exists an odd number $l \leq 3$ such that m.toNat = $p1*l$.
              · have hp1' : p1 ∣ m.toNat := by
                  refine Dvd.dvd.trans ?_ hp
                  exact Nat.dvd_of_mem_primeFactorsList (n := p) (p := p1) (by simp [p1])
                obtain ⟨l, hpl⟩ := hp1'
                have : Odd l := by
                  by_contra h
                  simp at h
                  suffices Even m.toNat by tauto
                  rw [hpl, Nat.even_mul]
                  simp [h]
                obtain ⟨k, hk⟩ := this
                use k - 1
                have hk' : k > 0 := by
                  by_contra h
                  have : k = 0 := by omega
                  rw [this, mul_zero, zero_add] at hk
                  rw [hk, mul_one] at hpl
                  rw [hpl] at hp2
                  linarith [Nat.le_of_mem_primeFactorsList (n := p) (p := p1) (by simp [p1])]
                simp [hpl, hk, mul_add, Nat.mul_sub]
                rw [← Nat.sub_add_comm]
                · omega
                · apply mul_le_mul (by linarith) (by omega) (by norm_num) (by norm_num)
        rcases h2 with (h2 | h2)
        -- If m.toNat is an even number greater than 2 then let $n = m / 2$, we have $b | \binomial{n}{0}$. This is a contradiction.
        · obtain ⟨k, hk, hmk⟩ := h2
          have h3 : (m / 3 : ℚ) ≤ k := by
            rw [div_le_iff₀ (by norm_num)]
            norm_cast
            have : m = Int.ofNat m.toNat := by
              simp only [Int.ofNat_eq_coe, ofNat_toNat]
              symm
              rw [max_eq_left_iff]
              linarith
            rw [this, hmk]
            simp
            linarith
          have h4 : k ≤ (m / 2 : ℚ) := by
            rw [le_div_iff₀ (by norm_num)]
            norm_cast
            rw [mul_comm, ← hmk]
            simp
            linarith
          specialize h k h3 h4
          rw [hmk, Nat.sub_self] at h
          simp at h
          linarith
        -- If m.toNat has an odd prime factor $p$ that is not equal to itself then let $n = \frac{m-p}{2}$, we have $n | \binomial{n}{p}$.
        · obtain ⟨p, hp, hp2, k, hmk⟩ := h2
          have h3 : (p * (k + 1) : ℕ) ≤ (m / 2 : ℚ) := by
            rw [le_div_iff₀ (by norm_num)]
            norm_cast
            trans (m.toNat : ℤ)
            · rw [hmk]
              norm_cast
              simp [mul_add, add_mul, ← mul_assoc, mul_comm]
              omega
            · simp
              linarith
          have h4 : (m / 3 : ℚ) ≤ (p * (k + 1) : ℕ) := by
            rw [div_le_iff₀ (by norm_num)]
            norm_cast
            trans (m.toNat : ℤ)
            · simp
            · rw [hmk]
              norm_cast
              simp [mul_add, add_mul, ← mul_assoc, mul_comm]
              omega
          specialize h (p * (k + 1)) h4 h3
          have hp' : p * (2 * k + 3) - 2 * (p * (k + 1)) = p := by
            simp [mul_add, ← mul_assoc]
            simp [mul_comm (a := p), ← Nat.sub_sub]
            omega
          rw [hmk, hp'] at h
          -- Casue $p$ is prime number, so $p \mid (n-1)(n-2)\cdots(n-p+1)$
          rw [Nat.choose_eq_descFactorial_div_factorial, Nat.dvd_div_iff_mul_dvd] at h
          · rw [← Nat.descFactorial_mul_descFactorial (k := 1) (by linarith)] at h
            simp at h
            rw [Nat.mul_dvd_mul_iff_right (by positivity), Nat.dvd_iff_dvd_dvd] at h
            specialize h p (by exact Nat.dvd_factorial (by linarith) (by linarith))
            rw [Nat.descFactorial_eq_prod_range, Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp)] at h
            simp [Nat.sub_sub] at h
            -- There is also $∀ a < p-1, p \nmid n-a$ which naturally follows $p \nmid (n-1)(n-2)\cdots(n-p+1)$, so we find a contradiction.
            suffices ∀ a < p - 1, ¬ p ∣ p * (k + 1) - (1 + a) by tauto
            intro a ha
            rw [← Nat.not_dvd_iff_between_consec_multiples _ (by linarith)]
            use k
            constructor
            · rw [mul_add, mul_one]
              omega
            · apply Nat.sub_lt_self (by omega)
              trans 1 + (p - 1)
              · linarith
              · rw [show 1 + (p - 1) = p by omega, mul_add]
                omega
          · use (p * (k + 1)).choose p
            exact Nat.descFactorial_eq_factorial_mul_choose (p * (k + 1)) p
    · simp
      linarith
  -- We check that all primes satisfy the condition, and even a stronger one. Namely, if $p$ is a prime then every $n$ with $1 \leq n \leq \frac{p}{2}$ divides $\left(\begin{array}{c}n \\ p-2 n\end{array}\right)$.
  · intro m hm
    simp at *
    obtain ⟨p, h1, h2⟩ := hm
    rw [← h2]
    simp at *
    constructor
    · exact Nat.Prime.two_le h1
    · intro n hn1 hn2
      -- Check whether $p$ is equal to $2*n$.
      by_cases h : p = 2 * n
      -- If $p = 2*n$, then $n = 1$, the divisibility relationship is established.
      · simp [h]
        have hp : Even p := by rw [h]; exact even_two_mul n
        rw [Nat.Prime.even_iff h1] at hp
        rw [hp] at h
        omega
      -- Prove if $p \neq 2n$, then $n \mid \binom{n}{p-2n}$.
      · have hn1 : p - 2 * n ≤ n := by
          simp
          rw [div_le_iff₀ (by norm_num)] at hn1
          norm_cast at hn1
          linarith
        have h0 : n > 0 := by
          by_contra! h0
          have h0 : n = 0 := by omega
          simp [h0] at hn1
          exact Nat.Prime.ne_zero h1 hn1
        have hn : 1 ≤ p - 2 * n := by
          by_contra! hpn
          have : p - 2 * n = 0 := by linarith
          rw [Nat.sub_eq_zero_iff_le] at this
          have : p < 2 * n := by omega
          rw [le_div_iff₀ (by norm_num)] at hn2
          norm_cast at hn2
          linarith
        -- If $p \neq 2n$, then $n \mid (p-2n) \binom{n}{p-2n}$.
        have h3 : n ∣ (p - 2 * n) * n.choose (p - 2 * n) := by
          use (n - 1).choose (p - 2 * n - 1)
          have := @Nat.choose_mul n (p - 2 * n) 1 hn1 hn
          simp at this
          rw [mul_comm, this]
        -- $n$ and $p-2n$ are relatively prime.
        have h4 : n.Coprime (p - 2 * n) := by
          by_contra! h₀
          simp at h₀
          have : n.gcd (p - 2 * n) ∣ p := by
            have := Dvd.dvd.linear_comb (Nat.gcd_dvd_left n (p - 2 * n)) (Nat.gcd_dvd_right n (p - 2 * n)) 2 1
            rw [show 2 * n + 1 * (p - 2 * n) = p by simp; omega] at this
            exact this
          rw [Nat.dvd_prime h1] at this
          rcases this with (this | this)
          · tauto
          · suffices n.gcd (p - 2 * n) < p by linarith
            apply LE.le.trans_lt
            · exact Nat.gcd_le_left (p - 2 * n) h0
            · omega
        -- and so the factor $n$ in the right-hand side divides the binomial coefficient $\left(\begin{array}{c}n \\ p-2 n\end{array}\right)$.
        exact Nat.Coprime.dvd_mul_left h4 |>.1 h3
