import Mathlib

/- A sequence of numbers is defined by $a_{n}=n^{4}-360 n^{2}+400$. Calculate the sum of all terms of this sequence that are prime numbers. -/

theorem algebra_211052 : ∑ᶠ n : ℕ, (if (Nat.Prime (n^4 - 360 * n^2 + (400 : ℤ)).natAbs)
    then (n^4 - 360 * n^2 + (400 : ℤ)) else 0) = 802 := by

  -- We will show that the only values of n for which the expression is prime are 1 and 19.
  have (n : ℕ) : Nat.Prime (n^4 - 360 * n^2 + (400 : ℤ)).natAbs ↔ n = 1 ∨ n = 19 := by
    constructor
    · -- If the expression is prime, then n must be either 1 or 19.
      intro hn
      -- We can factor the expression as (n^2 - 20 * n + 20)(n^2 + 20 * n + 20).
      have : (n^4 - 360 * n^2 + (400 : ℤ)) = (n^2 - 20 * n + 20) * (n^2 + 20 * n + 20) := by ring
      rw [this, Int.natAbs_mul, Nat.prime_mul_iff] at hn
      -- Since the expression is prime, one of the factors must be ±1.
      rcases hn with ⟨hp, h1⟩ | ⟨hp, h1⟩
      · -- If n^2 + 20 * n + 20 = ±1, then we can solve for n.
        rw [(by ring : (n^2 + 20 * n + (20 : ℤ) = (n + 1) * (n + 19) + 1)), Int.natAbs_eq_iff] at h1
        rcases h1 with h1 | h1
        · -- n^2 + 20 * n + 20 = 1 is not possible, as the LHS is always greater than or equal to 20.
          simp only [Nat.cast_one, add_left_eq_self, mul_eq_zero] at h1
          rcases h1 with h1 | h1
          all_goals omega
        · -- n^2 + 20 * n + 20 = -1 is also not possible, as the LHS is always positive.
          have : (↑n + 1) * (↑n + 19) + 1 > 0 := by positivity
          linarith
      · -- If n^2 - 20 * n + 20 = ±1, then we can solve for n.
        rw [(by ring : (n^2 - 20 * n + (20 : ℤ) = (n - 1) * (n - 19) + 1)), Int.natAbs_eq_iff] at h1
        rcases h1 with h1 | h1
        · -- If n^2 - 20 * n + 20 = 1, we get the solution n = 1 or n = 19.
          simp only [Nat.cast_one, add_left_eq_self, mul_eq_zero] at h1
          rcases h1 with h1 | h1
          · left
            rw [sub_eq_zero] at h1
            exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm h1)))
          · right
            rw [sub_eq_zero] at h1
            exact Eq.symm ((fun {m n} ↦ Int.ofNat_inj.mp) (id (Eq.symm h1)))
        · -- If n^2 - 20 * n + 20 = -1, there are no solutions by analyzing the equation modulo 4.
          simp only [Nat.cast_one, Int.reduceNeg] at h1
          have : (↑n - 1) * (↑n - 19) + 1 = (-1 : ZMod 4) := by rw_mod_cast [h1]
          mod_cases n % 4
          all_goals
            rw [← ZMod.eq_iff_modEq_nat] at H
            rw [H] at this
            norm_num at this
            contradiction
    · -- For n = 1 and n = 19, we can check that the expression is prime, as we get 41 and 761.
      intro h
      rcases h with h | h
      all_goals rw [h]; norm_num

  -- It follows that the summand is nonzero only for n = 1 and n = 19.
  have supp : (Function.support fun (n : ℕ) ↦ if n = 1 ∨ n = 19 then n ^ 4 - 360 * n ^ 2 + (400 : ℤ) else 0)
      = ({1, 19} : Finset ℕ) := by
    ext n
    constructor
    · -- As we have shown, the only values of n for which the expression is prime are 1 and 19.
      intro h
      simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at h
      simp [h]
    · -- Conversely, if n = 1 or n = 19, the expression is nonzero.
      intro h
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at h
      rcases h with h | h
      all_goals simp [h]

  -- We can now compute the sum of the terms of the sequence that are prime numbers.
  simp_rw [this]
  rw [finsum_eq_finset_sum_of_support_subset _ (subset_of_eq supp)]
  norm_num