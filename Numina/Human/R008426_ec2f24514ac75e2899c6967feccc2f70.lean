import Mathlib


/- A natural number is abundant if it is less than the sum of its proper divisors. What is the smallest abundant number? -/
theorem number_theory_15521
    (is_abundant : ℕ → Prop)
    (def_isabundant : is_abundant = fun n => n < n.properDivisors.sum id) :
    IsLeast {n | is_abundant n} 12 := by

  -- For any prime number, the sum of its proper divisors is equal to $1$, so a prime number cannot be an abundant number.
  have p_notabundant : ∀ p, p.Prime → ¬ is_abundant p := by
    intro p hp
    simp [def_isabundant]
    rw [← pow_one p, Nat.properDivisors_prime_pow hp]
    simp only [Finset.range_one, Finset.map_singleton, Function.Embedding.coeFn_mk, pow_zero,
      Finset.sum_singleton, pow_one]
    linarith only [Nat.Prime.two_le hp]

  -- Therefore, it suffices to check only composite numbers:
  have clt12: ∀ n < 12, ¬ is_abundant n := by
    intro n hn
    interval_cases n

    -- 0
    . simp [def_isabundant]

    -- 1
    . simp [def_isabundant]

    -- 2
    . exact p_notabundant 2 Nat.prime_two

    -- 3
    . exact p_notabundant 3 Nat.prime_three

    -- For $4$, $1 + 2 < 4$,
    . simp [def_isabundant, show Nat.properDivisors 4 = {1, 2} by rfl]

    -- 5
    . exact p_notabundant 5 Nat.prime_five

    -- For $6$, $1 + 2 + 3 = 6$,
    . simp [def_isabundant, show Nat.properDivisors 6 = {1, 2, 3} by rfl]

    -- 7
    . exact p_notabundant 7 (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)

    -- For $8$, $1 + 2 + 4 < 8$,
    . simp [def_isabundant, show Nat.properDivisors 8 = {1, 2, 4} by rfl]

    -- For $9$, $1 + 3 < 9$,
    . simp [def_isabundant, show Nat.properDivisors 9 = {1, 3} by rfl]

    -- For $10$, $1 + 2 + 5 < 10$,
    . simp [def_isabundant, show Nat.properDivisors 10 = {1, 2, 5} by rfl]

    -- 11
    . exact p_notabundant 11 (Nat.properDivisors_eq_singleton_one_iff_prime.mp rfl)

  -- For $12$, $1 + 2 + 3 + 4 + 6 = 16 > 12$.
  have c12 : is_abundant 12 := by
    simp [def_isabundant, show Nat.properDivisors 12 = {1, 2, 3, 4, 6} by rfl]

  -- Thus, the answer is $\boxed{12}$.
  unfold IsLeast
  constructor
  . simp [c12]
  . simp [lowerBounds, Set.mem_setOf_eq]
    intro n hn
    by_contra! h_contra
    exact clt12 n h_contra hn
