import Mathlib

/- Determine all the triplets $(p, q, r)$ of prime numbers such that $ p + q^2 = r^4 $. -/
theorem number_theory_607177 (p q r : ℕ) (hpqr : p.Prime ∧ q.Prime ∧ r.Prime) :
    p + q^2 = r^4 ↔ (p, q, r) = (7, 3, 2) := by
    constructor
    · intro h
      simp
      -- We note that the equation can be rewritten as $ p = (r^2)^2 - q^2 = (r^2 - q)(r^2 + q) $.
      have h1 : p = (r^2 - q) * (r^2 + q) := by
        apply Nat.eq_sub_of_add_eq at h
        rw [h, Nat.sub_mul, Nat.mul_add, Nat.mul_add, Nat.sub_add_eq, mul_comm q, Nat.add_sub_cancel, ← pow_two, ← pow_two, ← pow_mul]
      -- Since $ r^2 + q $ is strictly positive, and $ p $ is also, $ r^2 - q $ is also.
      have h2 : r^2 - q > 0 := by
        by_contra! hn
        aesop
      -- In particular, from the previous equation, we have $ r^2 - q = 1 $ and $ r^2 + q = p $.
      have h3 : r^2 - q = 1 := by
        have h31 : r^2 - q ∣ p := by use (r^2 + q)
        rw [Nat.dvd_prime hpqr.1] at h31
        rcases h31 with (h31 | h31)
        · exact h31
        · simp [h31] at h1
          suffices p > p by simp at this
          nth_rw 1 [h1]
          refine (Nat.lt_mul_iff_one_lt_right (by omega)).mpr ?_
          suffices 1 < q by omega
          exact Nat.prime_def_lt.1 hpqr.2.1 |>.1
      have h4 : r^2 + q = p := by
        simp [h3] at h1
        exact id (Eq.symm h1)
      by_cases hqr : Odd r ∧ Odd q
      -- If $ r $ and $ q $ are odd, then $ r^2 - q $ is even, which is contradictory.
      · suffices Even (r ^ 2 - q) by aesop
        apply Nat.Odd.sub_odd _ hqr.2
        apply Odd.pow hqr.1
      · -- Thus $ r $ or $ q $ is even, so both $ r = 2 $ or $ q = 2 $.
        have h5 : r = 2 ∨ q = 2 := by
          simp at hqr
          by_cases hr : Even r
          · left; rwa [Nat.Prime.even_iff hpqr.2.2] at hr
          · simp at hr
            specialize hqr hr
            right; rwa [Nat.Prime.even_iff hpqr.2.1] at hqr
        rcases h5 with (hr | hq)
        -- If $ r = 2 $, then $ r^2 - q = 1 $, so $ q = 4 - 1 = 3 $. Hence $ p = q + r^2 = 3 $, so $ (p, q, r) = (7, 3, 2) $ is a possible solution.
        · simp [hr] at h3
          refine ⟨?_, ⟨(by omega), hr⟩⟩
          rw [hr] at h4
          omega
        -- If $ q = 2 $, then $ r^2 = q + 1 = 3 $ which is impossible.
        · rw [hq] at h3
          have : Prime (r ^ 2) := by
            suffices r ^ 2 = 3 by rw [this]; refine Nat.prime_iff.mp ?_; exact Nat.prime_three
            omega
          simp [prime_pow_iff] at this
    -- Reciprocipally, for $ (p, q, r) = (7, 3, 2) $, $ p + q^2 = 7 + 9 = 16 = 2^4 $.
    · rintro ⟨rfl, rfl, rfl⟩
      norm_num