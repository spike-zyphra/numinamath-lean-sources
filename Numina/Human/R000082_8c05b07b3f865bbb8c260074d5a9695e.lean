import Mathlib

/- Find all prime numbers that can be expressed as the difference of
  the fourth powers of two integers. -/
theorem number_theory_4487 : {p : ℕ | p.Prime ∧ ∃ a b, p = a ^ 4 - b ^ 4} = ∅ := by
  ext p
  refine ⟨fun ⟨h, ⟨a, b, h'⟩⟩ => ?_, fun hp => ?_⟩
  -- there is no prime number can be expressed as a^4-b^4
  · -- deduce `b≤a` from `a^4-b^4=p≥2`
    have b_le_a : b ≤ a := by
      by_contra lt
      simp only [not_le] at lt
      rw [Nat.sub_eq_zero_of_le (by apply Nat.pow_le_pow_of_le_left; linarith)] at h'
      rw [h'] at h
      revert h
      decide
    -- factor `a^4-b^4` to `(a-b)(a+b)(a^2+b^2)`
    replace h' : p = (a - b) * (a + b) * (a ^ 2 + b ^ 2) := by
      rw [h']
      zify
      rw [Int.ofNat_sub (Nat.pow_le_pow_of_le_left b_le_a _), Int.ofNat_sub b_le_a]
      simp only [Nat.cast_pow]
      ring
    -- Notice that p is prime, it must be `a+b=1` or `a^2+b^2=1`
    have eq_1 : a + b = 1 ∨ a ^ 2 + b ^ 2 = 1 := by
      by_contra not_eq_1
      simp only [not_or] at not_eq_1
      exact Nat.not_prime_mul' h'.symm (mul_ne_one.mpr (.inr not_eq_1.1)) not_eq_1.2 h
    -- If `a=0,b=1` or `a=1,b=0`, then `p` is not prime.
    have (h : a = 0 ∧ b = 1 ∨ a = 1 ∧ b = 0) : p ∈ (∅ : Set _) := by
      rw [Nat.add_eq_one_iff] at eq_1
      rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      · simp only [ha, hb] at h'
        norm_num at h'
        rw [h'] at h
        revert h
        simp only [Set.mem_empty_iff_false, imp_false]
        decide
    cases' eq_1 with eq_1 eq_1
    -- a+b=1
    · rw [Nat.add_eq_one_iff] at eq_1
      exact this eq_1
    -- a^2+b^2=1
    · rw [Nat.add_eq_one_iff] at eq_1
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at eq_1
      repeat rw [pow_eq_one_iff (by norm_num)] at eq_1
      exact this eq_1
  · simp at hp
