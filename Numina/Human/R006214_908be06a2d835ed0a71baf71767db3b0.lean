import Mathlib
/- Let $p$ be an odd prime number. Natural numbers $a$ and $b$ are such that $a^{3}+b^{3}+p \cdot ab$ is divisible by $ab(a-b)$. Prove that $\operatorname{LCM}(a,b)$ is a perfect square. -/
theorem algebra_634706 (p a b : ℕ) (hp1 : Odd p) (hp2 : Nat.Prime p) (h : a * b * (a - b) ∣ a ^ 3 + b ^ 3 + p * a * b) : IsSquare (Nat.lcm a b) ∨ IsSquare (p * Nat.lcm a b):= by
  -- Case analysis: check if either a or b is zero
  by_cases h1 : a = 0 ∨ b = 0
  .
    -- Handle the case where a = 0 or b = 0
    rcases h1 with rfl | rfl
    all_goals
      simp at h
      subst h
      simp
  .
    -- Case analysis: check if a - b = 0
    by_cases h2 : a - b = 0
    .
      -- Handle the case where a = b
      rw [h2] at h
      simp at h
      omega
    .
      -- We have a > b, so we can work with gcd and lcm
      replace h2 : a > b:= by omega
      -- Set d as the greatest common divisor of a and b
      set d:= Nat.gcd a b with hd
      clear_value d
      -- Prove that d is positive
      have hdpos : d > 0:= by
        subst d
        refine Nat.gcd_pos_of_pos_left b (by omega)
      -- Prove that d divides a
      have g1 : d ∣ a:= by
        subst d
        exact Nat.gcd_dvd_left a b
      -- Prove that d divides b
      have g2 : d ∣ b:= by
        subst d
        exact Nat.gcd_dvd_right a b
      -- Express a and b in terms of d and coprime factors
      rcases g1 with ⟨a, rfl⟩
      rcases g2 with ⟨b, rfl⟩
      simp at h1
      replace h1 : a ≠ 0 ∧ b ≠ 0 ∧ d ≠ 0:= by omega
      -- Rewrite lcm in terms of d and coprime factors
      rw [show Nat.lcm (d * a) (d * b) = d * Nat.lcm a b by exact Nat.lcm_mul_left]
      -- Rewrite gcd in terms of d and coprime factors
      rw [show Nat.gcd (d * a) (d * b) = d * Nat.gcd a b by exact Nat.gcd_mul_left d a b] at hd
      -- Since d is the gcd, the remaining factors are coprime
      replace hd : Nat.gcd a b = 1:= by exact (Nat.mul_right_eq_self_iff hdpos).mp (id (Eq.symm hd))
      -- Maintain the inequality a > b
      replace h2 : a > b:= by exact (Nat.mul_lt_mul_left hdpos).mp h2
      -- Express a - b in terms of d
      have h3 : d * a - d * b = d * (a - b):= by
        set c:= a - b with hc
        clear_value c
        replace hc : a = b + c:= by omega
        subst a
        ring_nf
        omega
      -- Substitute the expression for a - b into the divisibility condition
      rw [h3] at h
      -- Rewrite the left side of the divisibility condition
      rw [show d * a * (d * b) * (d * (a - b)) = d ^ 2 * ((d * a * b) * (a - b)) by ring] at h
      -- Rewrite the right side of the divisibility condition
      rw [show (d * a) ^ 3 + (d * b) ^ 3 + p * (d * a) * (d * b) = d ^ 2 * (d * (a ^ 3 + b ^ 3) + p * a * b) by ring] at h
      -- Cancel d^2 from both sides
      replace h : d * a * b * (a - b) ∣ d * (a ^ 3 + b ^ 3) + p * a * b:= by
        replace hdpos : d ^ 2 > 0:= by positivity
        exact Nat.dvd_of_mul_dvd_mul_left hdpos h
      -- Simplify the divisibility condition
      replace h: d * a * b ∣ d * (a ^ 3 + b ^ 3) + p * a * b:= by exact dvd_of_mul_right_dvd h
      -- Since a and b are coprime, lcm(a,b) = a*b
      rw [show Nat.lcm a b = a * b by exact Nat.Coprime.lcm_eq_mul hd]
      -- Case analysis: check if p divides d
      by_cases h4 : p ∣ d
      .
        -- Case 1: p divides d
        rcases h4 with ⟨k, hk⟩
        rw [hk] at h
        -- Factor out p from the expression
        rw [show p * k * (a ^ 3 + b ^ 3) + p * a * b = p * (k * (a ^ 3 + b ^ 3) + a * b) by ring] at h
        rw [show p * k * a * b = p * (k * (a * b)) by ring] at h
        -- Cancel p from both sides
        replace h : k * (a * b) ∣ k * (a ^ 3 + b ^ 3) + a * b:= by
          have hppos : p > 0:= by exact Nat.Prime.pos hp2
          exact Nat.dvd_of_mul_dvd_mul_left hppos h
        -- Prove that k divides the right side
        have g1 : k ∣ k * (a ^ 3 + b ^ 3) + a * b:= by exact dvd_of_mul_right_dvd h
        -- Since k divides k*(a^3 + b^3), it must also divide a*b
        replace g1 : k ∣ a * b:= by
          have g2 : k ∣ k * (a ^ 3 + b ^ 3):= by exact Nat.dvd_mul_right k (a ^ 3 + b ^ 3)
          exact (Nat.dvd_add_iff_right g2).mpr g1
        -- Prove that a*b divides the right side
        have g2 : a * b ∣ k * (a ^ 3 + b ^ 3) + a * b:= by exact dvd_of_mul_left_dvd h
        -- Since a*b divides a*b, it must also divide k*(a^3 + b^3)
        replace g2 : a * b ∣ k:= by
          have g3 : a * b ∣ a * b:= by simp
          replace g2 : a * b ∣ k * (a ^ 3 + b ^ 3):= by exact (Nat.dvd_add_iff_left g3).mpr g2
          -- Since a*b divides k*(a^3 + b^3), a must divide k*(a^3 + b^3)
          replace g3 : a ∣ k * (a ^ 3 + b ^ 3):= by exact dvd_of_mul_right_dvd g2
          -- Express k*(a^3 + b^3) as a*(k*a^2) + k*b^3
          rw [show k * (a ^ 3 + b ^ 3) = a * (k * a ^ 2) + k * b ^ 3 by ring] at g3
          have g4 : a ∣ a * (k * a ^ 2):= by simp
          -- Since a divides a*(k*a^2), it must also divide k*b^3
          replace g3 : a ∣ k * b ^ 3:= by exact (Nat.dvd_add_iff_right g4).mpr g3
          -- Similarly, b must divide k*(a^3 + b^3)
          replace g4 : b ∣ k * (a ^ 3 + b ^ 3):= by exact dvd_of_mul_left_dvd g2
          -- Express k*(a^3 + b^3) as b*(k*b^2) + k*a^3
          rw [show k * (a ^ 3 + b ^ 3) = b * (k * b ^ 2) + k * a ^ 3 by ring] at g4
          have g5 : b ∣ b * (k * b ^ 2):= by simp
          -- Since b divides b*(k*b^2), it must also divide k*a^3
          replace g4 : b ∣ k * a ^ 3:= by exact (Nat.dvd_add_iff_right g5).mpr g4
          -- Use coprimality to show that a divides k
          replace hd : Nat.Coprime a b:= by exact hd
          have hd1 : Nat.Coprime b a:= by exact Nat.coprime_comm.mp hd
          have hd2 : Nat.Coprime a (b ^ 3):= by exact Nat.Coprime.pow_right 3 hd
          replace hd1 : Nat.Coprime b (a ^ 3):= by exact Nat.Coprime.pow_right 3 hd1
          replace g3 : a ∣ k:= by exact Nat.Coprime.dvd_of_dvd_mul_right hd2 g3
          -- Use coprimality to show that b divides k
          replace g4 : b ∣ k:= by exact Nat.Coprime.dvd_of_dvd_mul_right hd1 g4
          -- Since a and b are coprime and both divide k, a*b divides k
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hd g3 g4
        -- Since k divides a*b and a*b divides k, we have k = a*b
        replace h1 : k = a * b:= by exact Nat.dvd_antisymm g1 g2
        subst k
        -- Prove that p*LCM(a,b) is a perfect square
        right
        rw [hk]
        use p * a * b
        ring
      .
        -- Case 2: p does not divide d (p and d are coprime)
        replace h4 : Nat.Coprime p d:= by exact (Nat.Prime.coprime_iff_not_dvd hp2).mpr h4
        replace h4 : Nat.Coprime d p:= by exact Nat.coprime_comm.mp h4
        -- Factor out d from the left side
        rw [show d * a * b = d * (a * b) by ring] at h
        -- Prove that d divides the right side
        have g1 : d ∣ d * (a ^ 3 + b ^ 3) + p * a * b:= by exact dvd_of_mul_right_dvd h
        -- Since d divides d*(a^3 + b^3), it must also divide p*a*b
        replace g1 : d ∣ a * b:= by
          have g2 : d ∣ d * (a ^ 3 + b ^ 3):= by simp
          replace g2 : d ∣ p * a * b:= by exact (Nat.dvd_add_iff_right g2).mpr g1
          rw [show p * a * b = p * (a * b) by ring] at g2
          -- Since d and p are coprime, d must divide a*b
          exact Nat.Coprime.dvd_of_dvd_mul_left h4 g2
        -- Prove that a*b divides d
        have g2 : a * b ∣ d:= by
          replace h : a * b ∣ d * (a ^ 3 + b ^ 3) + p * a * b:= by exact dvd_of_mul_left_dvd h
          -- a*b divides p*a*b
          have g3 : a * b ∣ p * a * b:= by
            use p
            ring
          -- Since a*b divides p*a*b, it must also divide d*(a^3 + b^3)
          replace h : a * b ∣ d * (a ^ 3 + b ^ 3):= by exact (Nat.dvd_add_iff_left g3).mpr h
          -- Use coprimality properties to show that a*b divides d
          have h5 : Nat.Coprime a (b ^ 3):= by exact Nat.Coprime.pow_right 3 hd
          have h6 : Nat.Coprime b a:= by exact Nat.coprime_comm.mp hd
          replace h6 : Nat.Coprime b (a ^ 3):= by exact Nat.Coprime.pow_right 3 h6
          replace h5 : Nat.Coprime a (a * a ^ 2 + b ^ 3):= by exact (Nat.coprime_mul_left_add_right a (b ^ 3) (a ^ 2)).mpr h5
          replace h6 : Nat.Coprime b (b * b ^ 2 + a ^ 3):= by exact (Nat.coprime_mul_left_add_right b (a ^ 3) (b ^ 2)).mpr h6
          rw [show a * a ^ 2 + b ^ 3 = a ^ 3 + b ^ 3 by ring] at h5
          rw [show b * b ^ 2 + a ^ 3 = a ^ 3 + b ^ 3 by ring] at h6
          -- Since a and b are coprime, a*b is coprime with a^3 + b^3
          replace h5 : Nat.Coprime (a * b) (a ^ 3 + b ^ 3):= by exact Nat.Coprime.mul h5 h6
          -- Since a*b is coprime with a^3 + b^3 and divides d*(a^3 + b^3), it must divide d
          exact Nat.Coprime.dvd_of_dvd_mul_right h5 h
        -- Since d divides a*b and a*b divides d, we have d = a*b
        replace g1 : d = a * b:= by exact Nat.dvd_antisymm g1 g2
        subst d
        -- Prove that LCM(a,b) is a perfect square
        left
        use a * b
