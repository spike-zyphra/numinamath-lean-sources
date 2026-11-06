import Mathlib

/- Z2) Determine all natural numbers $n \geq 2$ that have a representation of the form


$$

n=k^{2}+d^{2}

$$


where $k$ is the smallest divisor of $n$ greater than 1 and $d$ is any divisor of $n$. -/
theorem number_theory_266018 {n : ℕ} (hn : n ≥ 2) :
    (∃ k d, n = k^2 + d^2 ∧ k = n.minFac ∧ d ∣ n) → n = 8 ∨ n = 20 := by
      --We'll first show that n cannot be odd.
      --The idea is that if n is odd, then all divisors of n, and in particular k and d must be odd.
      --So k^2 is odd, and so is d^2.
      --So their sum must be even.
      --But their sum n is odd by assumption.
      --Contradiction.
      intro h
      obtain ⟨k, d, h1, h2, h3⟩ := h
      have H0 : Even n := by
        by_contra h
        have H001 : Odd n := by exact Nat.not_even_iff_odd.mp h
        have H00 : Odd k := by
          by_contra hk
          have hk0 : Even k := by exact Nat.not_odd_iff_even.mp hk
          have hk1 : k = 2 := by
            have k_prime : Nat.Prime k := by
              have hn : n ≠ 1 := by omega
              rw [h2]
              apply Nat.minFac_prime
              exact hn
            exact (Nat.Prime.even_iff k_prime).mp hk0
          have : 2 ∣ n := by
            refine (Nat.minFac_eq_two_iff n).mp ?_
            rw [h2] at hk1
            exact hk1
          have : Even n := by exact (even_iff_exists_two_nsmul n).mpr this
          contradiction
        have d_odd : Odd d:= by
          have : d ∣ n := by exact h3
          exact Odd.of_dvd_nat H001 h3
        have h11 : Odd (k^2) := by exact Odd.pow H00
        have h12 : Odd (d^2) := by exact Odd.pow d_odd
        have h13 : Even n := by
          have : Even (k^2 + d^2) := by
            exact Odd.add_odd h11 h12
          rw [←h1] at this
          exact this
        contradiction
      --Hence it follows that k = 2.
      have k_2 : k = 2 := by
        have h5 : 2 ∣ n := by
          exact Nat.dvd_of_mod_eq_zero (id (Nat.even_iff.1 H0))
        have h6 : k ≤ 2 := by
          rw [h2]
          have h8 : n.minFac ≤ 2 := by
            apply Nat.minFac_le_of_dvd
            exact Nat.AtLeastTwo.prop
            exact h5
          linarith
        have h7 : k ≥ 2 := by
          rw [h2]
          have h9 : n.minFac ≥ 2 := by
            have hn' : n ≠ 1 := by omega
            exact Nat.minFac_prime hn' |>.two_le
          linarith
        linarith

      --Since n and k are even d must be even as well.
      have H1 : Even d := by
        by_contra h
        have H11 : Odd (d^2) := by
          refine Odd.pow ?_
          exact Nat.not_even_iff_odd.mp h
        have H12 : Even (k^2) := by
          rw [k_2]
          decide
        have H13 : Odd (k^2 + d^2) := by exact Even.add_odd H12 H11
        rw [←h1] at H13
        have : ¬ Even n := by exact Nat.not_even_iff_odd.mpr H13
        contradiction

      --Let t be such that d = 2t.
      obtain ⟨t, hdt⟩ := H1
      ring_nf at hdt
      rw [mul_comm] at hdt

      --So n = 4 + 4t^2
      have H2 : n = 4 + 4 * t^2 := by
        rw [k_2, hdt] at h1
        ring_nf at h1
        rw [mul_comm]
        exact h1

      --Since d is a divisor of n, 2t divides 4 + 4t^2.

      have H3 : 2 * t ∣ 4 + 4 * t^2 := by
        rw [hdt] at h3
        rw [H2] at h3
        exact h3

      --But this means t divides 2 + 2 * t^2.

      have H4 : t ∣ 2 + 2 * t^2 := by
        have : 2 * t ∣ 2 * (2 + 2 * t^2) := by
          have :  2 * (2 + 2 * t^2) = 4 + 4 * t^2 := by ring
          exact
            (Nat.ModEq.dvd_iff (congrFun (congrArg HMod.hMod (id (Eq.symm this))) (4 + 4 * t ^ 2))
                  H3).mp
              H3
        obtain ⟨m, hm⟩ := this
        have H41 :  (2 + 2 * t ^ 2) = t * m := by
          have : 2 * t * m = 2 * (t * m ) := by ring
          rw [this] at hm
          rw [mul_right_inj' (by norm_num : 2 ≠ 0)] at hm
          exact hm
        use m

      --Now this means t ∣ 2 (1 + t^2)
      have H5 : t ∣ 2 * (1 + t^2) := by
        have : 2 * (1 + t^2) = 2 + 2 * t^2 := by ring
        rw [this]
        exact H4

      --But gcd (t, t^2 + 1) = 1.
      have H6 : Nat.gcd t (t^2 + 1) = 1 := by
        have h1 : t.Coprime (t ^ 2 + 1) := by
          simp [Nat.Coprime]
          refine (Nat.coprime_add_iff_right ?_).mpr ?_
          exact Dvd.intro_left (t.pow 1) rfl
          exact Nat.gcd_one_right t
        exact h1

      --This mean t must divide 2.
      have H7 : t ∣ 2 := by
        have H5' : t ∣ 2 * (t^2 + 1) := by rwa [add_comm] at H5
        exact Nat.Coprime.dvd_of_dvd_mul_right H6 H5'

      --So t must be either 1 or 2.
      have H8 : t = 1 ∨ t = 2 := by
        have : t ∣ 2 := by exact H7
        refine (Nat.dvd_prime ?_).mp H7
        decide

      --Now we split into two cases.
      rcases H8 with H9|H10
      --case 1.
      --d must be 2
      have d_2 : d = 2 := by omega
      rw [k_2, d_2] at h1
      norm_num at h1
      left
      exact h1
      --Case 2 :
      --d must be 4.
      have d_4 : d = 4 := by omega
      rw [k_2, d_4] at h1
      norm_num at h1
      right
      exact h1