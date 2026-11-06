import Mathlib  


/-Let $b, n, m$ be natural numbers such that $b > 1$, $n > 1$, and $m \ge 1$.
Suppose that for every integer $k > 1$, there exists an integer $a$ such that $k$ divides $(b - m \cdot a^n)$.
Then $m$ divides $b$, and there exists a natural number $A$ such that $b = m \cdot A^n$.-/
theorem Number_Theory_641629 {b n m}
  (hb : (b : ℕ) > 1)
  (hn : n > 1)
  (hm : (m : ℕ) ≥ 1)
  (h_0 : ∀ k > 1, ∃ (a : ℤ), k ∣ (b - m * (a ^ n))) :
  m ∣ b ∧ ∃ A, b = m * (A ^ n) := 
by

  -- First half: prove m ∣ b.

  have h0 : m ∣ b := by
    -- Split on the trivial case m = 1.
    by_cases h : m = 1
    ·
      -- If m = 1, divisibility holds automatically.
      simp [h]
    ·
      -- Otherwise, use the hypothesis h_0 with k = m².
      specialize h_0 (m ^ 2) (by
        norm_cast
        -- Show 1 < m² using elementary facts.
        refine Nat.one_lt_pow ?_ ?_
        trivial
        omega)
      -- Unpack the witness (a, t) such that m² divides the target expression.
      obtain ⟨a, t, ht⟩ := h_0
      -- Convert to an ℤ-divisibility statement.
      have h1 : (m : ℤ) ∣ (b : ℤ) := by
        -- 1)  m ∣ (b - m*aⁿ)
        have h_sub : (m : ℤ) ∣ (↑b - ↑m * a ^ n) := by
          -- because m ∣ m²*t and ht says m²*t = …
          simpa [ht] using
            (show (m : ℤ) ∣ (↑m ^ 2 * t : ℤ) from ⟨(m * t : ℤ), by ring⟩)
        -- 2)  m ∣ m*aⁿ  (obvious)
        have h_mul : (m : ℤ) ∣ (↑m * a ^ n : ℤ) := ⟨a ^ n, by ring⟩
        -- 3)  hence m ∣ (b - m*aⁿ) + m*aⁿ = b
        simpa [sub_add_cancel] using dvd_add h_sub h_mul
      exact_mod_cast h1            
      -- back to ℕ-world

  -- We now have m ∣ b, store it and move on.

  constructor
  ·
    exact h0                      
    -- First goal: m divides b.
  ·
    -- Second goal: produce A such that b = m·Aⁿ.
    obtain ⟨c, hc⟩ := h0         
     -- Write b = m·c.
    simp [hc]

    -- Factorise c into primes to analyse its exponents.

    have h1 : c =
        ∏ p ∈ c.primeFactors, p ^ (c.factorization p) := by
      -- Standard identity: reconstruct c from its factorisation.
      have : (c.factorization.prod fun x1 x2 => x1 ^ x2) = c := by
        apply Nat.factorization_prod_pow_eq_self
        by_contra not
        simp [not] at hc
        linarith
      exact id (Eq.symm this)


    -- Key number-theoretic lemma:
    -- For every prime factor p of c, n divides v_p(c).

    have h2 : ∀ p ∈ c.primeFactors, n ∣ c.factorization p := by
      intro p hp
      -- Use h_0 with k = m·p^(v_p(c)+1) to force a divisibility on exponents.
      specialize h_0 (m * (p ^ (1 + c.factorization p))) (by
        refine one_lt_mul_of_le_of_lt ?_ ?_
        linarith
        refine one_lt_pow₀ ?_ ?_
        -- p is prime so p > 1.
        refine Nat.one_lt_cast.mpr ?_
        refine Nat.Prime.one_lt ?_
        exact Nat.prime_of_mem_primeFactors hp
        refine Nat.ne_zero_iff_zero_lt.mpr ?_
        exact Fin.pos'
        )
      obtain ⟨a, ha⟩ := h_0

      -- The rest is a (rather intricate) valuation argument:
      -- ultimately deducing n ∣ v_p(c).
      -- Convert the expression into ℤ and strip the obvious factor m.
      simp [hc, ←mul_sub,
            mul_dvd_mul_iff_left (show (m : ℤ) ≠ 0 by omega)] at ha

      -- We now distinguish two cases depending on whether p^(v_p(c)+1) divides aⁿ.
      by_cases h : (p ^ (1 + c.factorization p) : ℤ) ∣ a ^ n
      ·
        -- Case 1: high power divides aⁿ ⇒ contradiction with minimality,
        -- yielding n ∣ v_p(c).
        apply (Int.dvd_iff_dvd_of_dvd_sub ha).mpr at h
        have hc_low : ¬ (p ^ (c.factorization p + 1) ∣ c) := by
          refine Nat.pow_succ_factorization_not_dvd ?_ ?_
          -- (Technical refuting step)
          by_contra not
          simp [not] at hc
          linarith
          exact Nat.prime_of_mem_primeFactors hp
        -- Finish: contradiction reveals the desired divisibility.
        rw [add_comm] at h
        norm_cast at h
      ·
        -- Case 2: high power does NOT divide aⁿ.
        by_cases H : ¬ (p ^ (c.factorization p) : ℤ) ∣ a ^ n
        ·
          -- This branch ultimately leads to a contradiction,
          -- again implying n ∣ v_p(c).
          have h1 : (p ^ (c.factorization p) : ℤ) ∣ ↑c - a ^ n := by
            exact Int.dvd_trans
              (by norm_cast; refine Nat.pow_dvd_pow p (by linarith)) ha
          have h2 : (p ^ c.factorization p : ℤ) ∣ a ^ n := by
            exact (Int.dvd_iff_dvd_of_dvd_sub h1).mp
              (by norm_cast; exact Nat.ordProj_dvd c p)
          tauto
        ·
          -- Final algebraic valuation identity establishes that
          -- multiplicity_p(aⁿ) = n·multiplicity_p(a),
          -- and hence multiplicity_p(c) is a multiple of n.
          simp at H
          have h1 : c.factorization p =
              multiplicity (p : ℤ) (a ^ n) := by
            refine Eq.symm (multiplicity_eq_of_dvd_of_not_dvd H ?_)
            rw [add_comm]; exact h
          have h2 : multiplicity (p : ℤ) (a ^ n) =
              n * multiplicity (p : ℤ) a := by
            refine FiniteMultiplicity.multiplicity_pow ?_ ?_
            refine Nat.prime_iff_prime_int.mp ?_
            exact Nat.prime_of_mem_primeFactors hp
            refine Int.finiteMultiplicity_iff.mpr ?_
            constructor
            simp
            refine Nat.Prime.ne_one
              (by exact Nat.prime_of_mem_primeFactors hp)
            by_contra w
            simp [w, show (0 : ℤ) ^ n = 0 by
              exact pow_eq_zero_of_le hn rfl] at h
          -- Combine the equalities.
          rw [h2] at h1
          exact Dvd.intro (multiplicity (↑p) a) (id (Eq.symm h1))

  
    -- Build the required A: take c’s prime factors, but divide
    -- each exponent by n (which is possible by h2).
 
    use ∏ p ∈ c.primeFactors, p ^ (c.factorization p / n)

    -- Show b = m * (A ^ n).
    left
    nth_rw 1 [h1]
    -- Move the n-th power out of the product.
    have h1 :
      (∏ p ∈ c.primeFactors, p ^ (c.factorization p / n)) ^ n =
      ∏ p ∈ c.primeFactors, (p ^ (c.factorization p / n)) ^ n := by
      exact Eq.symm
        (Finset.prod_pow c.primeFactors n
          (fun x => x ^ (c.factorization x / n)))

    rw [h1]
    -- Finally, compare factors exponent-wise.
    apply Finset.prod_congr
    · trivial
    intro x hx
    simp [← pow_mul]
    rcongr
    exact Eq.symm (Nat.div_mul_cancel (h2 x hx))