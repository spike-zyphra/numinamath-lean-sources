import Mathlib

/-
4. Find all pairs of prime numbers $(p, q)$ for which


$$

7 p q^{2}+p=q^{3}+43 p^{3}+1

$$

 -/
theorem number_theory_173330 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : 7 * p * q ^ 2 + p = q ^ 3 + 43 * p ^ 3 + 1) :
    (p, q) = (2, 7)
  := by
    -- Consider p and q odd
    by_cases ho : Odd p ∧ Odd q
    · have ⟨hp, hq⟩ := ho

      -- Then one side of the equation is even
      have lo : Even (7 * p * q ^ 2 + p)
      · simp only [Nat.even_add', hp, iff_true, Nat.odd_mul, and_true, true_and, Odd.pow hq]
        decide

      -- And the other odd
      have ro : Odd (q ^ 3 + 43 * p ^ 3 + 1)
      · simp only [Nat.odd_add, Odd.pow hq, true_iff, Nat.not_even_one,
          iff_false, Nat.not_even_iff_odd, Nat.odd_mul, true_and, Odd.pow hp, and_true]
        decide

      -- Contradiction
      rw [h] at lo
      rw [← Nat.not_even_iff_odd] at ro
      exact False.elim (ro lo)

    -- So at least one is even
    have either_even : Even p ∨ (Even q ∧ Odd p)
    · simp only [not_and, Nat.not_odd_iff_even] at ho
      cases' Nat.even_or_odd p with pe po
      · exact Or.inl pe
      · refine Or.inr ?_
        exact ⟨ho po, po⟩

    -- Consider the two cases
    cases' either_even with pe hh
    -- If p is an even prime, then p = 2
    · have ju : p = 2 := (Nat.Prime.even_iff hp).mp pe
      subst ju

      -- Simplify and factorize
      simp only [Nat.reduceMul, Nat.reducePow, add_left_inj] at h
      have ff : q * (14 * q - q ^ 2) = 343
      · rw [Nat.mul_sub]
        ring_nf
        rw [mul_comm, h, add_tsub_cancel_left]

      -- Then we have that q ∣ 343 = 7 ^ 3, but then q = 7 so we're done.
      have yep : q ∣ 343
      · rw [←ff]
        exact Nat.dvd_mul_right q (14 * q - q ^ 2)
      have as_pow : 343 = 7 ^ 3 := by decide
      rw [as_pow] at yep
      rw [Nat.prime_eq_prime_of_dvd_pow hq (by decide) yep]
    · have ⟨qe, po⟩ := hh
      -- If q is an even prime, then q = 2
      have ju : q = 2 := (Nat.Prime.even_iff hq).mp qe
      subst ju

      -- We simplify and see that one side is odd and the other even.
      simp only [Nat.reducePow] at h
      ring_nf at h
      have lo : Odd (p * 29)
      · simp only [po, Nat.odd_mul, true_and]
        decide

      have re : Even (9 + p ^ 3 * 43)
      · simp only [Nat.even_add', Odd.pow po, Nat.odd_mul, true_and]
        decide

      -- Contradiction
      rw [h, ← Nat.not_even_iff_odd] at lo
      exact False.elim (lo re)