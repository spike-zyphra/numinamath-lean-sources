import Mathlib

/- Show that in the decimal system there is a 100-digit number divisible by $2^{100}$, which contains only the digits 1 and 2. -/

theorem number_theory_176633 : ∃ n : ℕ, (Nat.digits 10 n).length = 100 ∧
    2^100 ∣ n ∧ ∀ d ∈ (Nat.digits 10 n), d = 1 ∨ d = 2 := by

  -- We prove by induction on m that the statement holds for any m ≥ 1.
  have {m : ℕ} (h : 1 ≤ m) : ∃ n : ℕ, (Nat.digits 10 n).length = m ∧
    2^m ∣ n ∧ ∀ d ∈ (Nat.digits 10 n), d = 1 ∨ d = 2 := by

    induction' m, h using Nat.le_induction with m hm h
    · -- For m = 1, we can take n = 2.
      use 2
      all_goals simp
    · -- For m > 1, first we rewrite the induction hypothesis.
      obtain ⟨n, ⟨len, ⟨k, hk⟩, dig⟩⟩ := h
      -- We distinguish two cases based on the quotient of the division of n by 2^m.
      by_cases h : Even k
      · -- If k is even, then 2^(m+1) divides 2 * 10^m + n.
        use 2 * 10^m + n
        rw [← len, add_comm, mul_comm, ← Nat.digits_append_digits (by linarith)]
        refine ⟨?_, ?_, ?_⟩
        · simp
        · -- The quotient is 5^m + k / 2, which is integer because k is even.
          use 5^m + k / 2
          rw [len, mul_add, pow_add, pow_one, mul_assoc _ _ (k / 2), Nat.mul_div_cancel_left'
            (even_iff_two_dvd.mp h), mul_comm (2^m) 2, mul_assoc, ← mul_pow, ← hk]
          ring
        · intro d hd
          rw [List.mem_append] at hd
          rcases hd with hd | hd
          · exact dig d hd
          · simp only [Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
            Nat.reduceDiv, Nat.digits_zero, List.mem_singleton] at hd
            exact Or.inr hd
      · -- If k is odd, then 2^(m+1) divides 1 * 10^m + n.
        use 1 * 10^m + n
        rw [← len, add_comm, mul_comm, ← Nat.digits_append_digits (by linarith)]
        refine ⟨?_, ?_, ?_⟩
        · simp
        · -- The quotient is (5^m + k) / 2, which is integer because k is odd.
          use (5^m + k) / 2
          rw [len, pow_add, pow_one, mul_assoc, Nat.mul_div_cancel_left'
            (by rw [← even_iff_two_dvd]; apply Odd.add_odd (Odd.pow (by decide)) (Nat.not_even_iff_odd.mp h)),
            mul_add, ← mul_pow, ← hk]
          ring
        · intro d hd
          rw [List.mem_append] at hd
          rcases hd with hd | hd
          · exact dig d hd
          · simp only [Nat.reduceLeDiff, zero_lt_one, Nat.digits_of_two_le_of_pos, Nat.one_mod,
            Nat.reduceDiv, Nat.digits_zero, List.mem_singleton] at hd
            exact Or.inl hd
            
  -- Now we can apply the induction hypothesis to m = 100.
  exact this (by linarith : 100 > 0)