import Mathlib

/- Prove that for any positive integer $m$
there exist an infinite number of pairs of integers $(x, y)$ such that
(i) $x$ and $y$ are relatively prime;
(ii) $y$ divides $x^{2}+m$;
(iii) $x$ divides $y^{2}+m$. -/

theorem number_theory_24402 (m : ℕ) (hm : 0 < m):
    ∀ n, ∃ x y: ℕ, x > n ∧ y > n ∧ Nat.Coprime x y ∧
      y ∣ x ^ 2 + m ∧ x ∣ y ^ 2 + m := by

      intro n
      -- we prove a stronger statement by induction on n
      have h_strong: ∃ x y: ℕ, x < y ∧ x > n ∧ Nat.Coprime x y ∧
        y ∣ x ^ 2 + m ∧ x ∣ y ^ 2 + m := by
         induction' n with n ih
         -- base case
         .
            use 1
            use (1 + m)
            norm_num
            exact hm
         -- inductive step
         .
          obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := ih
          -- then we show that (y, y ^ 2 +  m / x) is a solution
          use y
          use ((y ^ 2 + m) / x)
          have l1: y < (y ^ 2 + m) / x := by
            rw [Nat.lt_div_iff_mul_lt']
            nlinarith
            exact h5
          simp [l1]
          clear l1
          have l2: n + 1 < y := by
            omega
          simp [l2]
          clear l2
          have d1: (y ^ 2 + m) / x ∣ y ^ 2 + m := by
            apply Nat.div_dvd_of_dvd
            exact h5
          simp [d1]
          clear d1
          constructor
          -- show coprime
          .
            rw [Nat.coprime_iff_gcd_eq_one]
            set d:= y.gcd ((y ^ 2 + m) / x)
            by_contra! h
            replace h: 2 ≤ d:= by
              have o: 0 < d := by
                simp [d]
                apply Nat.gcd_pos_of_pos_left
                linarith
              omega
            have d1: d ∣ y := by
              apply Nat.gcd_dvd_left
            have d2: d ∣ (y ^ 2 + m) / x := by
              apply Nat.gcd_dvd_right
            replace d2: d ∣ y ^ 2 + m := by
              have o1: (y ^ 2 + m) / x ∣ y ^ 2 + m := by
                apply Nat.div_dvd_of_dvd
                exact h5
              apply dvd_trans d2 o1

            --then we have d ∣ m
            have s1: d ∣ m := by
              rw [show m = y ^ 2 + m - y ^ 2 by omega]
              apply Nat.dvd_sub
              omega
              exact d2
              rw [show y ^ 2 = y * y by ring]
              have o2: y ∣ y * y := by simp
              apply dvd_trans d1 o2

            -- then we have d ∣ x ^ 2
            have s2: d ∣ x ^ 2 := by
              rw [show x ^ 2 = x ^ 2 + m - m by omega]
              apply Nat.dvd_sub
              omega
              apply dvd_trans d1 h4
              exact s1

            -- but x and y are coprime, so there is a contradiction
            have c: d ∣ y.gcd (x ^ 2) := by
              rw [Nat.dvd_gcd_iff]
              constructor
              .
                exact d1
              .
                exact s2
            have s: y.gcd (x ^ 2) = 1 := by
              rw [← Nat.coprime_iff_gcd_eq_one]
              apply Nat.Coprime.pow_right
              apply Nat.Coprime.symm
              exact h3
            rw [s] at c
            apply Nat.le_of_dvd at c
            linarith
            norm_num
          -- show y divides ((y ^ 2 + m) / x) ^ 2 + m
          .
            -- it suffices to show that y divides x ^ 2 * (((y ^ 2 + m) / x) ^ 2 + m)
            have s: y ∣ x ^ 2 * (((y ^ 2 + m) / x) ^ 2 + m) := by
              rw [show x ^ 2 * (((y ^ 2 + m) / x) ^ 2 + m) = x ^ 2 * ((y ^ 2 + m) / x) ^ 2 + x ^ 2 * m by ring]
              have eq: x ^ 2 * ((y ^ 2 + m) / x) ^ 2 = (y ^ 2 + m) ^ 2 := by
                rw [show x ^ 2 * ((y ^ 2 + m) / x) ^ 2 = (x * ((y ^ 2 + m) / x)) ^ 2 by ring]
                have o: x * ((y ^ 2 + m) / x) = y ^ 2 + m := by
                  rw [show x * ((y ^ 2 + m) / x) = ((y ^ 2 + m) / x) * x by ring]
                  rw [← Nat.dvd_iff_div_mul_eq]
                  exact h5
                rw [o]
              rw [eq]
              clear eq
              ring_nf
              rw [show y ^ 2 * m * 2 + y ^ 4 + m * x ^ 2 + m ^ 2 = y * (y * m * 2 + y ^ 3) + m * (x ^ 2 + m) by ring]
              apply Nat.dvd_add
              simp
              have o2: x ^ 2 + m ∣ m * (x ^ 2 + m) := by
                simp
              apply dvd_trans h4 o2

            apply Nat.Coprime.dvd_of_dvd_mul_left at s
            exact s
            apply Nat.Coprime.pow_right
            apply Nat.Coprime.symm
            exact h3


      --  then we can use the strong statement to get the original statement
      obtain ⟨x, y, h1, h2, h3, h4, h5⟩ := h_strong
      use x
      use y
      simp [h2, h4, h5]
      constructor
      .
        linarith
      .
        exact h3
        