import Mathlib

/- 4. Given are two prime numbers $p$ and $q$ that satisfy the condition $p < q < 2p$. Prove that there exist two consecutive natural numbers such that the greatest prime divisor of one of them is equal to $p$, and the greatest prime divisor of the other is equal to $q$.

 -/
theorem number_theory_104494 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : p < q ∧ q < 2 * p) :
    ∃ n, n > 0 ∧ IsGreatest (Nat.primeFactors n) p ∧
    (IsGreatest (Nat.primeFactors (n + 1)) q ∨ IsGreatest (Nat.primeFactors (n - 1)) q):= by
--Since p and q are different prime numbers, they are coprime.    
    have pq_coprime : gcd p q = 1 := by
      have : p ≠ q := by omega
      rw [← Nat.coprime_primes hp hq] at this
      exact this
--We now prove the main lemma of this problem, that is we can write 1 as a linear combination of p and q, where the coefficient of p is between -(q-1)/2 and (q-1)/2.    
    have : ∃ a b : ℤ, - q + 1 ≤ 2 * a ∧ 2 * a ≤ q - 1 ∧ a * p = b * q + 1 := by
      set a1 := Nat.gcdA p q with ha1
--We use the equality a1 = q * (q.bdiv a1) + (q.bmod a1), where a1 is the coefficient of p in the linear combination given by the extended Euclidean algorithm for the gcd of p and q, bmod denotes the remainder of the division (by q) with the property that it is bewteen -q/2 and q/2, and bdiv is the unique integer satisfying the equality.
      have a1eq : a1 = q * (a1.bdiv q) + (a1.bmod q) := by
        unfold Int.bdiv Int.bmod
        simp only [mul_ite, mul_zero]
        by_cases h' : q = 0
        · exfalso
          exact Nat.Prime.ne_zero hq h'
        · simp only [h', ↓reduceIte]
          by_cases h'' : a1 % ↑q < (↑q + 1) / 2
          · simp only [h'', ↓reduceIte]
            exact Eq.symm (Int.ediv_add_emod a1 ↑q)
          · simp only [h'', ↓reduceIte]
            ring_nf
            exact Eq.symm (Int.ediv_add_emod a1 ↑q)
--We use this refined version of the Euclidean algorithm to prove the main lemma.            
      use (a1.bmod q)
      use (- Int.gcdB p q - p * a1.bdiv q)
      constructor
      · unfold Int.bmod
        simp only [mul_ite, neg_add_le_iff_le_add]
        by_cases h' : a1 % ↑q < (↑q + 1) / 2
        · simp only [h', ↓reduceIte]
          rw [(by omega : (1 : ℤ) = 1 + 0)]
          gcongr
          · have : q ≠ 0 := Nat.Prime.ne_zero hq
            omega
          · simp only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
            refine Int.emod_nonneg a1 ?_
            exact_mod_cast Nat.Prime.ne_zero hq
        · simp only [h', ↓reduceIte]
          ring_nf
          simp only [not_lt] at h'
          have : q + 1 ≤ a1 % ↑q * 2 := by
            have : q ≠ 2 := by
              have : 2 < q := by
                apply lt_of_le_of_lt _ h.1
                exact Nat.Prime.two_le hp
              omega
            have := Nat.Prime.odd_of_ne_two hq this
            have : 2 ∣ q + 1 := by
              have : Even (q + 1) := by
                simp [this]
              rw [even_iff_two_dvd] at this
              exact this
            obtain ⟨k, hk⟩ := this
            rw_mod_cast [hk] at h' ⊢
            ring_nf
            simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.ofNat_pos, mul_le_mul_right, ge_iff_le]
            simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀] at h'
            exact h'
          omega          
--We are left to show that (a1.bmod q) and (- Int.gcdB p q - p * a1.bdiv q) work.   
      · constructor
        · unfold Int.bmod
          have : a1 % q < q := by
              nth_rw 2 [(by simp : (q : ℤ) = |(q : ℤ)| )]
              apply Int.emod_lt a1
              exact_mod_cast Nat.Prime.ne_zero hq
          by_cases h' : a1 % ↑q < (↑q + 1) / 2
          all_goals
            simp only [h', ↓reduceIte]
            omega
        · zify at pq_coprime
          have : (gcd p q)= p.gcd q := rfl
          rw [this, Nat.gcd_eq_gcd_ab p q, ← ha1, a1eq] at pq_coprime
          ring_nf
          rw [← pq_coprime]
          ring_nf
          simp only [self_eq_add_right]
          rw [sub_eq_zero]
          congr
--We know rewrite the gcd condition on p and q as the new equality ap = bq + 1          
    obtain ⟨a,b,ha1,ha2,hab⟩ := this
--The integer n will be |a| * p.    
    use Int.natAbs a * p
--It follows from the equality and the fact that p and q are prime numbers (thus larger than 1), that a and b are nonzero.    
    have anezero : a ≠ 0 := by
      intro hazero
      rw [hazero] at hab
      ring_nf at hab
      symm at hab
      rw [add_comm, ← sub_neg_eq_add, sub_eq_zero] at hab
      have qdvd1 : (q : ℤ) ∣ 1 := by use -b; linarith
      have : Prime q := by rw [← Nat.prime_iff]; exact hq
      apply Prime.not_dvd_one this
      exact_mod_cast qdvd1
    have bnezero : b ≠ 0 := by
      intro hbzero
      rw [hbzero] at hab
      ring_nf at hab
      have pdvd1 : (p : ℤ) ∣ 1 := by use a; linarith
      have : Prime p := by rw [← Nat.prime_iff]; exact hp
      apply Prime.not_dvd_one this
      exact_mod_cast pdvd1
    by_cases apos : a > 0
--If a>0, we have n=ap and the other number is n-1=bq. We prove that b is positive.    
    · have bpos : 0 < b := by
        have : a * p > 0 := by
          apply Int.mul_pos
          · omega
          · exact_mod_cast Nat.Prime.pos hp
        rw [hab] at this
        have : b * q ≥ 0 := by omega
        simp_rw [Int.mul_nonneg_iff] at this
        omega
--We then prove that n and n-1 satisfy the conditions of the problem.        
      · constructor
--We prove that n is positive.        
        · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.mul_pos, Int.natAbs_pos]
          constructor
          · intro h; omega
          · exact Nat.Prime.pos hp
        · constructor
--Then we prove that the greatest prime divisor of n is p.          
          · rw [Nat.primeFactors_mul (by rw [Int.natAbs_ne_zero]; omega) (Nat.Prime.ne_zero hp), IsGreatest]
            constructor
--We use the fact that the prime divisors of a product are the prime divisors of either factor. In particular, p divides the factor p.
            · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Nat.mem_primeFactors, Int.natAbs_eq_zero, dvd_refl, true_and]
              right
              exact ⟨hp,Nat.Prime.ne_zero hp⟩
            · simp only [Finset.coe_union, upperBounds_union, Set.mem_inter_iff]
              constructor
--To prove that p is an upperbound for the prime factors of a, we prove that in fact a ≤ p.              
              · have : q - 1 ≤ 2 * p := by omega
                have : a ≤ p := by omega
                rw [upperBounds]
                simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, and_imp, Set.mem_setOf_eq]
                intro p' hp' hpdvd hpnezero
                have : p' ≤ a := by
                  apply Nat.le_of_dvd at hpdvd
                  · omega
                  · simp only [Int.natAbs_pos, ne_eq]
                    omega
                omega
--Since p is prime, its largest prime factor is p.           
              · rw [upperBounds]
                simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, and_imp, Set.mem_setOf_eq]
                intro p' hp' hpdvd hpnezero
                rw [Nat.dvd_prime hp] at hpdvd
                simp [Nat.Prime.ne_one hp'] at hpdvd
                omega
--We now prove that the largest factor of n - 1 = bq is q.                 
          · right
            have : (a.natAbs * p - 1) = b.natAbs * q := by
              have aeq := Int.natAbs_eq a
              have beq := Int.natAbs_eq b
              rcases aeq with aeq | aeq
              · rcases beq with beq | beq
                · rw [aeq, beq] at hab
                  rw_mod_cast [hab]
                  omega
                · omega
              · omega
            rw [this]
--Again we write the prime factors of bq as the union of the prime factors of b and q.            
            rw [Nat.primeFactors_mul (by rw [Int.natAbs_ne_zero]; omega) (Nat.Prime.ne_zero hq), IsGreatest]
            constructor
--We prove that q is a prime factor of bq, since it divides q.            
            · simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, dvd_refl, true_and]
              right
              exact ⟨hq,Nat.Prime.ne_zero hq⟩
--We prove that q is an upperbound for the prime factors of bq.              
            · simp only [Finset.coe_union, upperBounds_union, Set.mem_inter_iff]
              constructor
--For b, we have that b < q, which follows from the equality bq = ap - 1 and the fact that p < q < 2p.              
              · have : b * q ≤ a * p := by omega
                have : 2 * a * p ≤ p * q := by
                  rw [mul_comm]
                  gcongr
                  omega
                have : 2 * b * q ≤ p * q := by
                  apply le_trans _ this
                  rw [mul_assoc, mul_assoc]
                  gcongr
                have : 2 * b ≤ p := by
                  apply Int.le_of_mul_le_mul_right this (by exact_mod_cast Nat.Prime.pos hq)
                have : b < q := by omega
                rw [upperBounds]
                simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, and_imp, Set.mem_setOf_eq]
                intro q' hq' hqdvd hbnezero
                have : q' ≤ b := by
                  apply Nat.le_of_dvd at hqdvd
                  · omega
                  · simp only [Int.natAbs_pos, ne_eq]
                    exact hbnezero
                omega
--For q, the result follows once again from the fact that q is prime.                
              · rw [upperBounds]
                simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, and_imp, Set.mem_setOf_eq]
                intro q' hq' hqdvd hqnezero
                rw [Nat.dvd_prime hq] at hqdvd
                simp [Nat.Prime.ne_one hq'] at hqdvd
                omega
--We now consider the case where a < 0. In this case we also have b < 0. We will then have n = |a| * p and n + 1 = |b| * q. These will be the two consecutive numbers we are looking for. The proof is the same as in the previous case.
    · simp only [gt_iff_lt, not_lt] at apos
      have bneg : b < 0 := by
        have : a * p < 0 := by
          rw [mul_neg_iff]
          right
          constructor
          · omega
          · exact_mod_cast Nat.Prime.pos hp
        rw [hab] at this
        by_contra bpos
        simp only [gt_iff_lt, not_lt] at bpos
        have : q > 0 := Nat.Prime.pos hq
        have : b * q ≥ 0 := by simp_rw [mul_nonneg_iff]; simp only [Nat.cast_nonneg, and_true, Nat.cast_nonpos]; left; exact bpos
        linarith
      constructor
      · simp only [gt_iff_lt, CanonicallyOrderedCommSemiring.mul_pos, Int.natAbs_pos, ne_eq]
        constructor
        · exact anezero
        · exact Nat.Prime.pos hp
      · constructor
        · unfold IsGreatest
          constructor
          · rw [Nat.primeFactors_mul (by simp [anezero]) (Nat.Prime.ne_zero hp)]
            simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Nat.mem_primeFactors, ne_eq, Int.natAbs_eq_zero, dvd_refl, true_and]
            right
            exact ⟨hp,Nat.Prime.ne_zero hp⟩
          · rw [upperBounds]
            simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, mul_eq_zero, Int.natAbs_eq_zero, not_or, and_imp, Set.mem_setOf_eq]
            intro p' hp' hpdvd hanezero hpnezero
            rw [Nat.Prime.dvd_mul hp'] at hpdvd
            rcases hpdvd with hpdvd | hpdvd
            · have : p' ≤ a.natAbs := by
                apply Nat.le_of_dvd
                · omega
                · exact hpdvd
              apply le_trans this
              omega
            · apply Nat.le_of_dvd
              · exact Nat.Prime.pos hp
              · exact hpdvd
        · have eq : b.natAbs * q = a.natAbs * p + 1 := by
            have : b = - b.natAbs := by
              rw [← neg_eq_iff_eq_neg]
              symm
              refine (Int.natAbs_inj_of_nonneg_of_nonpos ?_ ?_).mp rfl
              · simp
              · omega
            rw [this] at hab
            have : a = - a.natAbs := by
              rw [← neg_eq_iff_eq_neg]
              symm
              refine (Int.natAbs_inj_of_nonneg_of_nonpos ?_ ?_).mp rfl
              · simp
              · omega
            rw [this] at hab
            ring_nf at hab
            omega
          left
          unfold IsGreatest
          constructor
          · rw [← eq]
            simp only [Finset.mem_coe, Nat.mem_primeFactors, dvd_mul_left, ne_eq, mul_eq_zero, Int.natAbs_eq_zero, not_or, true_and]
            constructor
            · exact hq
            · constructor
              · omega
              · exact Nat.Prime.ne_zero hq
          · rw [← eq, upperBounds]
            simp only [Finset.mem_coe, Nat.mem_primeFactors, ne_eq, mul_eq_zero, Int.natAbs_eq_zero, not_or, and_imp, Set.mem_setOf_eq]
            intro p' hp' hpdvd hbnezero hpnezero
            rw [Nat.Prime.dvd_mul hp'] at hpdvd
            rcases hpdvd with hpdvd | hpdvd
            · have : p' ≤ b.natAbs := by
                apply Nat.le_of_dvd
                · omega
                · exact hpdvd
              have aux : p' * q ≤ b.natAbs * q := by gcongr
              rw [eq] at aux
              have : a.natAbs ≤ q := by omega
              have : p' * q ≤ p * q + 1 := by
                apply le_trans aux
                gcongr
                · omega
                · omega
              have : p' * q ≠ p * q + 1 := by
                by_contra h'
                have : q ∣ 1 := by
                  zify at h' ⊢
                  use (p' - p)
                  rw [mul_sub, mul_comm (q : ℤ) (p' : ℤ), h']
                  ring_nf
                exact Nat.Prime.not_dvd_one hq this
              have : p' * q ≤ p * q := by omega
              have : p' ≤ p := by 
                rw [mul_le_mul_right (Nat.Prime.pos hq)] at this
                exact this
              apply le_trans this
              omega
            · apply Nat.le_of_dvd
              · exact Nat.Prime.pos hq
              · exact hpdvd