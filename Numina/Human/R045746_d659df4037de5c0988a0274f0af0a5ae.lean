import Mathlib

/- In this problem, we are asked to provide another proof of the infinitude of prime numbers.
  We start by assuming that there are only finitely many prime numbers, which we denote as \( p_1, p_2, \ldots, p_n \).
  We then construct a new integer \( Q \) defined as \( Q = p_1 p_2 \cdots p_n + 1 \). The goal is to
  show that \( Q \) has a prime factor that is not included in the original list of primes. From this,
  we will conclude that there must be infinitely many prime numbers. -/
theorem number_theory_4490 : ¬{x | Nat.Prime x}.Finite := by
  intro fin
  -- Define the number `Q`
  let Q := (∏ p ∈ fin.toFinset, p) + 1
  -- All elements in the finite list of prime numbers can't divide `Q`.
  have : ∀ p ∈ fin.toFinset, ¬p ∣ Q := by
    intro p hp
    simp only [Q, Nat.dvd_iff_mod_eq_zero]
    rw [Nat.add_mod]
    nth_rw 2 [Nat.mod_eq_zero_of_dvd]
    · simp only [zero_add, dvd_refl, Nat.mod_mod_of_dvd]
      rw [Nat.mod_eq_of_lt]
      · simp
      · by_contra h
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hp
        absurd hp
        replace h : p = 0 ∨ p = 1 := by omega
        cases' h with h h <;> (rw [h]; decide)
    · exact Finset.dvd_prod_of_mem _ hp
  -- Then `Q` must have a prime factor not in the list.
  replace : ∃ p, p ∣ Q ∧ p.Prime ∧ p ∉ fin.toFinset := by
    have not_nil := Q.primeFactorsList_eq_nil.not.mpr <| by
      simp only [AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
        add_left_eq_self, false_or, Q]
      rw [Finset.prod_eq_zero_iff]
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, exists_eq_right]
      decide
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ not_nil
    simp only [Nat.mem_primeFactorsList', ne_eq, Nat.add_one_ne_zero,
      not_false_eq_true, and_true] at hp
    refine ⟨p, hp.2, hp.1, fun h => this _ h hp.2⟩
  -- So we can derive a contradiction.
  simp at this
