import Mathlib

/- 4. Let the natural numbers $m$ and $n$ have exactly 101 divisors (counting 1 and the numbers themselves as divisors). Prove that it is not possible for $mn$ to have 1000 divisors. -/
theorem number_theory_214320 {m n : ℕ} (hm : m.divisors.card = 101) (hn : n.divisors.card = 101)
    (hmn : (m * n).divisors.card = 1000) : False := by

  -- We need to write the prime factorization of a number.
  have prime_factor {n : ℕ} (hn : n ≠ 0) : ∏ x ∈ n.primeFactors, x ^ (n.factorization x) = n := by
    rw [← Nat.prod_factorization_eq_prod_primeFactors (fun x y => x ^ y)]
    exact Nat.factorization_prod_pow_eq_self hn

  -- A product of numbers is odd if and only if all the numbers are odd.
  have odd_prod (s : Finset ℕ) (f : ℕ → ℕ): Odd (∏ x ∈ s, f x) ↔ ∀ x ∈ s, Odd (f x) := by
    constructor
    -- If the product is odd, then all the factors are odd.
    -- By contradiction, if one of the factors is even, then the product is even.
    · intro h x hx
      by_contra! hx'
      apply Nat.not_even_iff_odd.mpr h
      rw [Finset.prod_eq_mul_prod_diff_singleton hx f]
      exact Even.mul_right (Nat.not_odd_iff_even.mp hx') (∏ x ∈ s \ {x}, f x)
    -- If all the factors are odd, then the product is odd.
    -- By induction on the size of the set of factors, we can show that the product is odd.
    · intro h
      induction' s using Finset.induction_on with x xs hx ih
      · simp
      · rw [Finset.prod_insert hx]
        apply Odd.mul
        · simp [h]
        · apply ih; intro y hy
          exact h y (Finset.mem_insert_of_mem hy)

  -- The number of divisors of a number is odd if and only if the number is a square.
  have {n : ℕ} (hn : n ≠ 0) : Odd (n.divisors.card) ↔ IsSquare n := by
    constructor
    -- If the number of divisors is odd, then the number is a square.
    -- In fact, the number of divisors is the product of the exponents in the prime factorization plus one.
    -- If this product is odd, then all the exponents are even, so the number is a square.
    · intro h
      simp_rw [Nat.card_divisors hn, odd_prod, ← Nat.not_even_iff_odd, Nat.even_add_one, not_not] at h
      use ∏ x ∈ n.primeFactors, x ^ ((n.factorization x) / 2)
      rw [← Finset.prod_mul_distrib]
      have (x : ℕ) : 2 * (n.factorization x / 2) = n.factorization x := by
        by_cases hx : x ∈ n.primeFactors
        · exact Nat.two_mul_div_two_of_even (h x hx)
        · rw [Finsupp.not_mem_support_iff.mp hx]; ring
      simp_rw [← pow_add, ← two_mul, this]
      exact Eq.symm ((fun {a b} ↦ Nat.succ_inj'.mp) (congrArg Nat.succ (prime_factor hn)))
    -- If the number is a square, then the number of divisors is odd.
    -- Again, the number of divisors is the product of the exponents in the prime factorization plus one.
    -- If the number is a square, then all the exponents are even, so the product is odd.
    · intro ⟨k, hk⟩
      rw [Nat.card_divisors hn, odd_prod]
      intro x hx
      have k0 : k ≠ 0 := by intro hk'; apply hn; rw [hk, hk', zero_mul]
      simp [hk, Nat.factorization_mul k0 k0]

  -- Now both m and n have exactly 101 divisors, so they are both squares. But the product of two squares is a square, so mn is a square. This means that the number of divisors of mn is odd, but we have that the number of divisors of mn is 1000, which is even. This is a contradiction.
  have m0 : m ≠ 0 := by intro h; rw [h] at hm; simp at hm
  have n0 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
  have mn0 : m * n ≠ 0 := by intro h; rw [h] at hmn; simp at hmn
  obtain ⟨m', hm'⟩ := (this m0).mp (by rw [hm]; decide)
  obtain ⟨n', hn'⟩ := (this n0).mp (by rw [hn]; decide)
  have := (this mn0).mpr (by use m' * n'; rw [hm', hn']; ring)
  rw [hmn] at this
  contradiction